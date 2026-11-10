/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Chain.FromPbHelpers
public import LibsignalBinary.Proofs.SpqrV1.Chain.ChainPbCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpoch
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChain
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Chain.FromPbDecodes
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Join-Point and Cleanup Proofs for `<spqr::chain::Chain>::from_pb`

Proves the normal and tail-dealloc epilogues, the `direction >= 2` error block (`+292 .. +356`),
the join-point cleanup and success paths (`fromPb_join_err`, `fromPb_join_ok`), and relocatable
`[LibsignalPlacement]` slice drop glue (Blocks `287` and `288`) for `<spqr::chain::Chain>::from_pb`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Layout.L26
open Lean Elab Tactic ProofLib ProofLib.CodeLookup in
elab "code_fetches_sym " codeId:ident decPrefix:ident b:term:max H:term:max sym:str len:num : tactic => do
  let codeName ← realizeGlobalConstNoOverloadWithInfo codeId
  let eOff ← lookup codeName .fnOff sym.getString
  let hfn := mkCIdentFrom sym eOff.decl
  let offStx := Syntax.mkNumLit (toString eOff.val)
  evalTactic (← `(tactic| code_fetches $codeId $decPrefix $b $H $hfn $offStx $len))
end CryptoVerification.SpqrV1.Layout.L26

namespace CryptoVerification.SpqrV1.ChainProofs

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Layout.L26
open FromPbDecodes

set_option maxRecDepth 800000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

/-- Stack below `[s0.sp - 192#64 .. s0.sp)` (`chainFromPbStackX - 192 = 16608`). -/
abbrev chainFromPbSubStack : Nat := 16608

/-! ## Callee Offset Helpers -/

theorem dropProtoEpochSlice_rel_fromPb (b : BitVec 64) (ext : String → Option (State → State)) :
    (dropProgAtExt b ext).fnAddr dropProtoEpochSliceName =
      (dropProgAtExt b ext).fnAddr chainFromPbName +
        bv% (2 ^ 64 - ls_rel% "core::ptr::drop_glue::<[spqr::proto::pq_ratchet::chain::Epoch]>" "<spqr::chain::Chain>::from_pb") := by
  change b + BitVec.ofNat 64 (libsignalSessionCode.fnOff dropProtoEpochSliceName) =
    b + BitVec.ofNat 64 (libsignalSessionCode.fnOff chainFromPbName) +
      bv% (2 ^ 64 - ls_rel% "core::ptr::drop_glue::<[spqr::proto::pq_ratchet::chain::Epoch]>" "<spqr::chain::Chain>::from_pb")
  rw [show libsignalSessionCode.fnOff dropProtoEpochSliceName = num% (ls_off% "core::ptr::drop_glue::<[spqr::proto::pq_ratchet::chain::Epoch]>") from (ls_lemma% fnOff "core::ptr::drop_glue::<[spqr::proto::pq_ratchet::chain::Epoch]>"),
      show libsignalSessionCode.fnOff chainFromPbName = num% (ls_off% "<spqr::chain::Chain>::from_pb") from (ls_lemma% fnOff "<spqr::chain::Chain>::from_pb")]
  bv_omega

theorem dropChainEpochSliceLocal2_rel_fromPb (b : BitVec 64) (ext : String → Option (State → State)) :
    (dropProgAtExt b ext).fnAddr dropChainEpochSliceLocal2Name =
      (dropProgAtExt b ext).fnAddr chainFromPbName +
        bv% (2 ^ 64 - ls_rel% "core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#2]" "<spqr::chain::Chain>::from_pb") := by
  change b + BitVec.ofNat 64 (libsignalSessionCode.fnOff dropChainEpochSliceLocal2Name) =
    b + BitVec.ofNat 64 (libsignalSessionCode.fnOff chainFromPbName) +
      bv% (2 ^ 64 - ls_rel% "core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#2]" "<spqr::chain::Chain>::from_pb")
  rw [show libsignalSessionCode.fnOff dropChainEpochSliceLocal2Name = num% (ls_off% "core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#2]") from (ls_lemma% fnOff "core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#2]"),
      show libsignalSessionCode.fnOff chainFromPbName = num% (ls_off% "<spqr::chain::Chain>::from_pb") from (ls_lemma% fnOff "<spqr::chain::Chain>::from_pb")]
  bv_omega

theorem rustDealloc_rel_fromPb (b : BitVec 64) (ext : String → Option (State → State)) :
    (dropProgAtExt b ext).fnAddr "__rustc::__rust_dealloc" =
      (dropProgAtExt b ext).fnAddr chainFromPbName +
        bv% (ls_rel% "<spqr::chain::Chain>::from_pb" "__rustc::__rust_dealloc") := by
  change b + BitVec.ofNat 64 (libsignalSessionCode.fnOff "__rustc::__rust_dealloc") =
    b + BitVec.ofNat 64 (libsignalSessionCode.fnOff chainFromPbName) +
      bv% (ls_rel% "<spqr::chain::Chain>::from_pb" "__rustc::__rust_dealloc")
  rw [show libsignalSessionCode.fnOff "__rustc::__rust_dealloc" = num% (ls_off% "__rustc::__rust_dealloc") from (ls_stub% "__rustc::__rust_dealloc"),
      show libsignalSessionCode.fnOff chainFromPbName = num% (ls_off% "<spqr::chain::Chain>::from_pb") from (ls_lemma% fnOff "<spqr::chain::Chain>::from_pb")]
  bv_omega

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem div_112_magic_nat_eq {k : Nat} (hk : k * 112 < 2 ^ 63) :
    (BitVec.ofNat 64 (k * 112) >>> 4) * 0x6db6db6db6db6db7#64 = BitVec.ofNat 64 k :=
  div_112_magic_eq hk

@[local simp, local arm64_norm, local wp_norm]
private theorem sub_self_lsr4_mul_magic (a : BitVec 64) :
    ((a - a) >>> 4) * 0x6db6db6db6db6db7#64 = 0#64 := by
  rw [BitVec.sub_self]; rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem sub_self_lsr4_bv_mul_magic (a : BitVec 64) :
    ((a - a) >>> 4#64) * 0x6db6db6db6db6db7#64 = 0#64 := by
  rw [BitVec.sub_self]; rfl

private theorem csel_ult_sub_zero_of_le (n : Nat) (cap : BitVec 64) (hle : n ≤ cap.toNat) :
    (if (BitVec.ofNat 64 n).ult cap = true then 0#64
     else BitVec.ofNat 64 n - cap) = 0#64 := by
  have hn : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_of_le_of_lt hle cap.isLt)]
  by_cases hlt : n < cap.toNat
  · have hult : (BitVec.ofNat 64 n).ult cap = true := by simp [BitVec.ult, hn, hlt]
    simp [hult]
  · have heq : n = cap.toNat := by omega
    have hbv : BitVec.ofNat 64 n = cap := by rw [heq, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [hbv, BitVec.sub_self]
    cases (cap.ult cap) <;> rfl

private theorem pool_entails_empty_arrayAt_pool {α : Type} (A : RustAlloc)
    (elem : α → BitVec 64 → SepProp) (stride : Nat) (ptr : BitVec 64) :
    A.pool ⊢ arrayAt elem stride ptr [] ∗ A.pool :=
  Entails.of_eq (emp_sepConj A.pool).symm

/-! ## Stack Frame and Callee-Saved Helpers -/

/-- The 12 callee-saved registers stored at `[s0.sp - 96#64 .. s0.sp)`. -/
def calleeSavedFromPbAt (s0 : State) : SepProp :=
  ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .lr) ∗
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)

theorem calleeSavedFromPbAt_entails_memRegion_96 (s0 : State) :
    calleeSavedFromPbAt s0 ⊢ memRegion (s0.sp - 96#64) 96 := by
  unfold calleeSavedFromPbAt
  rw [ProofLib.memRegion_split' (b := s0.sp - 96#64) (n := 8) (k := 88) (b' := s0.sp - 88#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := s0.sp - 88#64) (n := 8) (k := 80) (b' := s0.sp - 80#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := s0.sp - 80#64) (n := 8) (k := 72) (b' := s0.sp - 72#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := s0.sp - 72#64) (n := 8) (k := 64) (b' := s0.sp - 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := s0.sp - 64#64) (n := 8) (k := 56) (b' := s0.sp - 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := s0.sp - 56#64) (n := 8) (k := 48) (b' := s0.sp - 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := s0.sp - 48#64) (n := 8) (k := 40) (b' := s0.sp - 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := s0.sp - 40#64) (n := 8) (k := 32) (b' := s0.sp - 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := s0.sp - 32#64) (n := 8) (k := 24) (b' := s0.sp - 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := s0.sp - 24#64) (n := 8) (k := 16) (b' := s0.sp - 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := s0.sp - 16#64) (n := 8) (k := 8) (b' := s0.sp - 8#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
          (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
            (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
              (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
                (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
                  (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
                    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
                      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
                        (ProofLib.pointsTo64_entails_memRegion _ _)))))))))))

/-- The 96-byte scratch region `[s0.sp - 192#64 .. s0.sp - 96#64)` at the join point (`+792`). -/
def joinScratchAt (s0 : State) (g : ChainPBGhost) (pb : ChainPB) (sp0_val : BitVec 64) : SepProp :=
  ((s0.sp - 192#64) ↦₆₄ sp0_val) ∗ memRegion (s0.sp - 184#64) 8 ∗
  ((s0.sp - 176#64) ↦₆₄ BitVec.ofNat 64 pb.nextRoot.length) ∗
  ((s0.sp - 168#64) ↦₆₄ pb.currentEpoch) ∗ ((s0.sp - 160#64) ↦₆₄ pb.sendEpoch) ∗
  memRegion (s0.sp - 152#64) 4 ∗ ((s0.sp - 148#64) ↦₃₂ pb.direction) ∗
  memRegion (s0.sp - 144#64) 32 ∗
  ((s0.sp - 112#64) ↦₆₄ g.linksCap) ∗ ((s0.sp - 104#64) ↦₆₄ g.linksPtr)

theorem joinScratchAt_entails_memRegion_96 (s0 : State) (g : ChainPBGhost) (pb : ChainPB)
    (sp0_val : BitVec 64) :
    joinScratchAt s0 g pb sp0_val ⊢ memRegion (s0.sp - 192#64) 96 := by
  unfold joinScratchAt
  rw [ProofLib.memRegion_split' (b := s0.sp - 192#64) (n := 8) (k := 88) (b' := s0.sp - 184#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := s0.sp - 184#64) (n := 8) (k := 80) (b' := s0.sp - 176#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := s0.sp - 176#64) (n := 8) (k := 72) (b' := s0.sp - 168#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := s0.sp - 168#64) (n := 8) (k := 64) (b' := s0.sp - 160#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := s0.sp - 160#64) (n := 8) (k := 56) (b' := s0.sp - 152#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := s0.sp - 152#64) (n := 4) (k := 52) (b' := s0.sp - 148#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := s0.sp - 148#64) (n := 4) (k := 48) (b' := s0.sp - 144#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := s0.sp - 144#64) (n := 32) (k := 16) (b' := s0.sp - 112#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := s0.sp - 112#64) (n := 8) (k := 8) (b' := s0.sp - 104#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (Entails.refl _)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
          (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
            (sepConj_mono (Entails.refl _)
              (sepConj_mono (ProofLib.pointsTo32_entails_memRegion _ _)
                (sepConj_mono (Entails.refl _)
                  (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
                    (ProofLib.pointsTo64_entails_memRegion _ _)))))))))

theorem restore_stack_192_chainFromPb (s0 : State) :
    memRegion (s0.sp - 192#64) 96 ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack ⊢ stackAt s0.sp chainFromPbStackX := by
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left (calleeSavedFromPbAt_entails_memRegion_96 s0))) ?_
  have h192 : memRegion (s0.sp - 192#64) 96 ∗ memRegion (s0.sp - 96#64) 96 =
      memRegion (s0.sp - 192#64) 192 :=
    (ProofLib.memRegion_split' (b := s0.sp - 192#64) (n := 96) (k := 96)
      (b' := s0.sp - 96#64) rfl (by bv_omega) (by decide)).symm
  rw [← sepConj_assoc, h192, sepConj_comm]
  change memRegion (s0.sp - 192#64 - 16608#64) 16608 ∗ memRegion (s0.sp - 192#64) 192 ⊢
    memRegion (s0.sp - 16800#64) 16800
  have hbase : s0.sp - 192#64 - 16608#64 = s0.sp - 16800#64 := by bv_omega
  rw [hbase]
  exact Entails.of_eq (ProofLib.memRegion_split' (b := s0.sp - 16800#64)
    (n := 16608) (k := 192) (b' := s0.sp - 192#64) rfl (by bv_omega) (by decide)).symm

theorem stackAt_subStack_split_dropStack32 (sp : BitVec 64) :
    stackAt (sp - 192#64) chainFromPbSubStack =
      memRegion (sp - 16800#64) 12480 ∗ stackAt (sp - 192#64) dropStack32 := by
  unfold stackAt chainFromPbSubStack dropStack32 allocHookStack
  have hbase : sp - 192#64 - BitVec.ofNat 64 16608 = sp - 16800#64 := by bv_omega
  rw [hbase]
  exact ProofLib.memRegion_split' (b := sp - 16800#64) (n := 12480) (k := 4128)
    (b' := sp - 192#64 - BitVec.ofNat 64 (4096 + 32)) rfl (by bv_omega) (by decide)

theorem stackAt_subStack_split_allocHook (sp : BitVec 64) :
    stackAt (sp - 192#64) chainFromPbSubStack =
      memRegion (sp - 16800#64) 12512 ∗ stackAt (sp - 192#64) allocHookStack := by
  unfold stackAt chainFromPbSubStack allocHookStack
  have hbase : sp - 192#64 - BitVec.ofNat 64 16608 = sp - 16800#64 := by bv_omega
  rw [hbase]
  exact ProofLib.memRegion_split' (b := sp - 16800#64) (n := 12512) (k := 4096)
    (b' := sp - 192#64 - BitVec.ofNat 64 4096) rfl (by bv_omega) (by decide)

/-! ## `VecDeque` Slice-Length `csel` Lemmas -/

theorem csel_sub_zero_of_le (n : Nat) (cap : BitVec 64) (hle : n ≤ cap.toNat) :
    (if !((BitVec.ofNat 64 n).toNat ≥ cap.toNat) then 0#64
     else BitVec.ofNat 64 n - cap) = 0#64 := by
  have hn : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_of_le_of_lt hle cap.isLt)]
  rw [hn]
  by_cases hlt : n < cap.toNat
  · have hge : ¬(n ≥ cap.toNat) := by omega
    simp [hge]
  · have heq : n = cap.toNat := by omega
    have hge : n ≥ cap.toNat := by omega
    have hbv : BitVec.ofNat 64 n = cap := by rw [heq, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simp [hge, hbv]

theorem csel_min_eq_of_le (n : Nat) (cap : BitVec 64) (hle : n ≤ cap.toNat) :
    (if !(cap.toNat ≥ (BitVec.ofNat 64 n).toNat) then cap
     else BitVec.ofNat 64 n) = BitVec.ofNat 64 n := by
  have hn : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_of_le_of_lt hle cap.isLt)]
  rw [hn]; have hge : cap.toNat ≥ n := hle; simp [hge]

theorem csel_ult_min_eq_of_le (n : Nat) (cap : BitVec 64) (hle : n ≤ cap.toNat) :
    (if cap.ult (BitVec.ofNat 64 n) = true then cap
     else BitVec.ofNat 64 n) = BitVec.ofNat 64 n := by
  have hn : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_of_le_of_lt hle cap.isLt)]
  have hult : cap.ult (BitVec.ofNat 64 n) = false := by
    simp [BitVec.ult, hn]; omega
  simp [hult]

theorem csel_zero_if_ptr_eq (ptr : BitVec 64) (n : Nat) (hn : n * 112 < 2 ^ 63) :
    (if (ptr + BitVec.ofNat 64 (n * 112) - ptr == 0#64) = true then 0#64
     else BitVec.ofNat 64 n) = BitVec.ofNat 64 n := by
  have hsub : ptr + BitVec.ofNat 64 (n * 112) - ptr = BitVec.ofNat 64 (n * 112) := by bv_omega
  rw [hsub]
  by_cases hn0 : n = 0
  · subst hn0; simp
  · have hne : (BitVec.ofNat 64 (n * 112) == 0#64) = false := by
      rw [beq_eq_false_iff_ne]; intro heq
      have hto := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hto
      change n * 112 = 0 at hto; omega
    simp [hne]

theorem csel_eq_zero_if_ptr_eq (ptr : BitVec 64) (n : Nat) (hn : n * 112 < 2 ^ 63) :
    (if (ptr + BitVec.ofNat 64 (n * 112) == ptr) = true then 0#64
     else BitVec.ofNat 64 n) = BitVec.ofNat 64 n := by
  by_cases hn0 : n = 0
  · subst hn0; simp
  · have hne : (ptr + BitVec.ofNat 64 (n * 112) == ptr) = false := by
      rw [beq_eq_false_iff_ne]; intro heq
      have h0 : BitVec.ofNat 64 (n * 112) = 0#64 := by
        rw [← sub_ptr_self_add_mul_112 ptr n, heq, BitVec.sub_self]
      have hto := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hto
      change n * 112 = 0 at hto; omega
    simp [hne]

@[local simp, local arm64_norm, local wp_norm]
theorem csel_both_zero (b : Bool) :
    (if b then 0#64 else 0#64) = 0#64 := by cases b <;> rfl

theorem bitvec_low_byte_clear_zero (w : BitVec 64) :
    BitVec.extractLsb' 0 8 (w &&& 0xffffffffffffff00#64 ||| 0#64) = 0#8 := by bv_bits

theorem sub_links_rem_112 (ptr : BitVec 64) (a b total : Nat) (h : a + 1 + b = total) :
    (ptr + BitVec.ofNat 64 (total * 112) - (ptr + BitVec.ofNat 64 ((a + 1) * 112))) =
      BitVec.ofNat 64 (b * 112) := by
  subst h; simp only [Nat.add_mul, BitVec.ofNat_add]; bv_omega

theorem sub_links_conv_112 (ptr : BitVec 64) (a : Nat) :
    ptr + BitVec.ofNat 64 (a * 112) - ptr = BitVec.ofNat 64 (a * 112) := by bv_omega

theorem err_stateDecode_pack_words (A : RustAlloc) (out : BitVec 64) (pb : ChainPB)
    (hfromPb : Chain.fromPb pb = .error .stateDecode)
    (w1 w2 w3 : BitVec 64) (hlow : BitVec.extractLsb' 0 8 w1 = 0#8) :
    (out ↦₆₄ 0xffffffffffffffff#64) ∗ ((out + 8#64) ↦₆₄ w1) ∗
      ((out + 16#64) ↦₆₄ w2) ∗ ((out + 24#64) ↦₆₄ w3) ∗ memRegion (out + 32#64) 56 ⊢
      chainResultAt A out (Chain.fromPb pb) := by
  rw [hfromPb]; exact chainErrorAt_stateDecode_of_lowByte_zero A out w1 w2 w3 hlow

/-! ## Epilogue Lemmas (`0x604e8` and `0x60464`) -/

abbrev fromPbRetPost (A : RustAlloc) (x : ChainFromPbCall) (s0 : State) : State → SepProp → Prop :=
  fun sf P' =>
    (sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) ∧
      (P' ⊢ ⌜sf.trace = s0.trace⌝ ∗ chainResultAt A x.out (Chain.fromPb x.pb) ∗
        memRegion x.pbPtr 80 ∗ A.pool ∗ stackAt s0.sp chainFromPbStackX)

def TraceCalleeSaved (s s0 : State) : Prop :=
  s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0

theorem fromPb_epilogue_ret {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (x : ChainFromPbCall) (s0 s : State)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (dropProgAtExt b ext).fnAddr chainFromPbName + 1140#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0) :
    SepWP (dropProgAtExt b ext) (s0.readReg64 .lr) s
      (chainResultAt A x.out (Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗ A.pool ∗
        memRegion (s0.sp - 192#64) 96 ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  rcases htr with ⟨htr, hvregs⟩
  code_fetches_sym libsignalSessionCode libsignalSessionBin b (Rust.withPanics ext) "<spqr::chain::Chain>::from_pb" 1184
  dsimp only [dropProgAtExt, chainFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::chain::Chain>::from_pb" = entry
  examples_hide_fetches
  unfold calleeSavedFromPbAt
  wp_steps
  refine SepWP.focus_weaken (restore_stack_192_chainFromPb s0) (by
    unfold calleeSavedFromPbAt; sep_focus) ?_
  wp_done

theorem fromPb_epilogue_dealloc {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (x : ChainFromPbCall) (s0 s : State) (nrCap nrPtr : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hnr_ne : nrCap ≠ 0) (_hnr_lt : nrCap.toNat < 2 ^ 63) (_hnr_ptr : nrPtr ≠ 0)
    (hpc : s.pc = (dropProgAtExt b ext).fnAddr chainFromPbName + 1008#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 .x0 = nrPtr) (hx1 : s.readReg64 .x1 = nrCap) :
    SepWP (dropProgAtExt b ext) (s0.readReg64 .lr) s
      (chainResultAt A x.out (Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗ A.pool ∗
        A.live nrPtr nrCap.toNat 1 ∗ memRegion nrPtr nrCap.toNat ∗
        memRegion (s0.sp - 192#64) 96 ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr chainFromPbName + bv% (ls_rel% "<spqr::chain::Chain>::from_pb" "__rustc::__rust_dealloc")) (rustDeallocSpec A) :=
    sub_ok_of_addr_eq (rustDealloc_rel_fromPb b ext) hdealloc
  have hnr_pos : nrCap.toNat > 0 := Nat.pos_of_ne_zero (by
    intro h0; exact hnr_ne (BitVec.eq_of_toNat_eq (by simpa using h0)))
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  rcases htr with ⟨htr, hvregs⟩
  code_fetches_sym libsignalSessionCode libsignalSessionBin b (Rust.withPanics ext) "<spqr::chain::Chain>::from_pb" 1184
  dsimp only [dropProgAtExt, chainFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc_raw hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::chain::Chain>::from_pb" = entry
  examples_hide_fetches
  unfold calleeSavedFromPbAt
  wp_steps
  refine SepWP.focus_weaken (restore_stack_192_chainFromPb s0) (by
    unfold calleeSavedFromPbAt; sep_focus) ?_
  rw [stackAt_chainFromPb_split_allocHook s0.sp]
  wp_call hdealloc_raw (nrPtr, nrCap.toNat, 1)
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_chainFromPb_split_allocHook s0.sp).symm)
    (by sep_focus) ?_
  wp_done

/-! ## Bad `direction >= 2` Branch (`0x60198 .. 0x601d8`, `+292 .. +356`) -/

set_option maxHeartbeats 800000 in
theorem fromPb_bad_direction {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (x : ChainFromPbCall) (s0 s : State)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hdir_uge : BitVec.ule 2#32 x.pb.direction = true)
    (hlen : x.gPb.epochs.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (_hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (dropProgAtExt b ext).fnAddr chainFromPbName + 292#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hx24 : s.readReg64 .x24 = x.out) (hx25 : s.readReg64 .x25 = x.pbPtr) :
    SepWP (dropProgAtExt b ext) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochPBAt A) 112 x.gPb.linksPtr (x.gPb.epochs.zip x.pb.links) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        memRegion (s0.sp - 192#64) 96 ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  have hep_ret := @fromPb_epilogue_ret A b ext x s0
  have hep_dealloc := @fromPb_epilogue_dealloc A b ext hdealloc x s0
  have hslice_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr chainFromPbName + bv% (2 ^ 64 - ls_rel% "core::ptr::drop_glue::<[spqr::proto::pq_ratchet::chain::Epoch]>" "<spqr::chain::Chain>::from_pb"))
      (dropProtoEpochSliceSpec A) :=
    sub_ok_of_addr_eq (dropProtoEpochSlice_rel_fromPb b ext) (drop_proto_epoch_slice_ok_ext hdealloc)
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr chainFromPbName + bv% (ls_rel% "<spqr::chain::Chain>::from_pb" "__rustc::__rust_dealloc")) (rustDeallocSpec A) :=
    sub_ok_of_addr_eq (rustDealloc_rel_fromPb b ext) hdealloc
  have hlen_lt : x.pb.links.length * 112 < 2 ^ 63 :=
    lt_of_le_of_lt (Nat.mul_le_mul_right 112 hl_le) hl_lt
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  have hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode :=
    chainFromPb_of_direction_uge_two hdir_uge
  refine SepWP.focus_weaken
    (arrayAt_chainEpochPBAt_entails_protoRepr A x.gPb.epochs x.pb.links x.gPb.linksPtr hlen)
    (by sep_focus) ?_
  refine SepWP.focus_weaken
    (vecU8BufAt_entails_dealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot hn_le hn_lt)
    (by sep_focus) ?_
  rw [memRegion_88_words4_rest x.out]
  wp_pull_exists
  code_fetches_sym libsignalSessionCode libsignalSessionBin b (Rust.withPanics ext) "<spqr::chain::Chain>::from_pb" 1184
  dsimp only [dropProgAtExt, chainFromPbName, dropProtoEpochSliceSpec,
    ProtoRepr.chainEpochPBSize, BitVec.ofNat_eq_ofNat] at hep_ret hep_dealloc hslice_raw hdealloc_raw hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::chain::Chain>::from_pb" = entry
  examples_hide_fetches
  refine seq_clean (mid := entry + 316#64)
    (P_mid := chainResultAt A x.out (Chain.fromPb x.pb) ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
      memRegion x.gPb.linksPtr (x.pb.links.length * 112) ∗
      linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecCapPtrDealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗ A.pool ∗
      memRegion (s0.sp - 192#64) 96 ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .x19 = x.gPb.linksPtr ∧ sm.readReg64 .x25 = x.pbPtr) ?_ ?_
  · unfold chainPBHeadersAt
    rw [stackAt_subStack_split_dropStack32 s0.sp]
    wp_steps
    refine SepWP.focus_weaken
      (err_stateDecode_pack_words A x.out x.pb hfromPb_eq _ _ _ (bitvec_low_byte_clear_zero _))
      (by sep_focus) ?_
    wp_call hslice_raw ⟨x.gPb.linksPtr, x.pb.links⟩
    rw [hsp]; wp_done
  · rintro s1 hpc1 hrun1 ⟨hsp1, htr1, hx19_1, hx25_1⟩
    refine SepWP.focus_weaken
      (linksRawAllocAt_combine_memRegion A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length hl_le hl_lt)
      (by sep_focus) ?_
    refine seq_clean (mid := entry + 344#64)
      (P_mid := chainResultAt A x.out (Chain.fromPb x.pb) ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        vecCapPtrDealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗ A.pool ∗
        memRegion (s0.sp - 192#64) 96 ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
        sm.readReg64 .x25 = x.pbPtr) ?_ ?_
    · unfold chainPBHeadersAt
      by_cases hc : x.gPb.linksCap = 0
      · have hcb : (x.gPb.linksCap == 0#64) = true := beq_iff_eq.mpr hc
        simp only [hcb, ↓reduceIte, emp_sepConj, sepConj_emp]; wp_steps; wp_done
      · have hcb : (x.gPb.linksCap == 0#64) = false := beq_eq_false_iff_ne.mpr hc
        have hpos : x.gPb.linksCap.toNat * 112 > 0 := by
          have : x.gPb.linksCap.toNat > 0 := Nat.pos_of_ne_zero (by
            intro hz; exact hc (BitVec.eq_of_toNat_eq (by simpa using hz)))
          omega
        have hlsl := cap_mul_112_shift_eq x.gPb.linksCap hl_lt
        simp only [hcb, Bool.false_eq_true, ↓reduceIte]
        rw [stackAt_subStack_split_allocHook s0.sp]
        wp_steps
        wp_call hdealloc_raw (x.gPb.linksPtr, x.gPb.linksCap.toNat * 112, 8)
        rw [hsp1]; wp_done
    · rintro s2 hpc2 hrun2 ⟨hsp2, htr2, hx25_2⟩
      by_cases hnr : x.gPb.nextRoot.cap = 0
      · have hnrb : (x.gPb.nextRoot.cap == 0#64) = true := beq_iff_eq.mpr hnr
        unfold vecCapPtrDealloc
        simp only [hnrb, ↓reduceIte, emp_sepConj, sepConj_emp]
        refine seq_clean (mid := entry + 1140#64)
          (P_mid := chainResultAt A x.out (Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗ A.pool ∗
            memRegion (s0.sp - 192#64) 96 ∗ calleeSavedFromPbAt s0 ∗
            stackAt (s0.sp - 192#64) chainFromPbSubStack)
          (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0) ?_ ?_
        · unfold chainPBHeadersAt; wp_steps
          refine SepWP.focus_weaken
            (chainPBHeadersAt_entails_memRegion_80 x.pbPtr x.gPb x.pb)
            (by unfold chainPBHeadersAt; sep_focus) ?_
          wp_done
        · rintro s3 hpc3 hrun3 ⟨hsp3, htr3⟩
          exact hep_ret s3 hsp0_align hpc3 hrun3 hsp3 htr3
      · have hnrb : (x.gPb.nextRoot.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hnr
        unfold vecCapPtrDealloc
        simp only [hnrb, Bool.false_eq_true, ↓reduceIte]
        refine seq_clean (mid := entry + 1008#64)
          (P_mid := chainResultAt A x.out (Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗ A.pool ∗
            A.live x.gPb.nextRoot.ptr x.gPb.nextRoot.cap.toNat 1 ∗
            memRegion x.gPb.nextRoot.ptr x.gPb.nextRoot.cap.toNat ∗
            memRegion (s0.sp - 192#64) 96 ∗ calleeSavedFromPbAt s0 ∗
            stackAt (s0.sp - 192#64) chainFromPbSubStack)
          (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
            sm.readReg64 .x0 = x.gPb.nextRoot.ptr ∧ sm.readReg64 .x1 = x.gPb.nextRoot.cap) ?_ ?_
        · unfold chainPBHeadersAt; wp_steps
          refine SepWP.focus_weaken
            (chainPBHeadersAt_entails_memRegion_80 x.pbPtr x.gPb x.pb)
            (by unfold chainPBHeadersAt; sep_focus) ?_
          wp_done
        · rintro s3 hpc3 hrun3 ⟨hsp3, htr3, hx0_3, hx1_3⟩
          exact hep_dealloc s3 x.gPb.nextRoot.cap x.gPb.nextRoot.ptr
            hsp0_align hnr hn_lt hn_ne hpc3 hrun3 hsp3 htr3 hx0_3 hx1_3

/-! ## Join-Point Error Path `fromPb_join_err` (`0x6038c .. 0x60504`, `w19 = 0`) -/

set_option maxHeartbeats 800000 in
theorem fromPb_join_err_tail {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (x : ChainFromPbCall) (s0 s : State)
    (convEpochs : List ChainEpoch) (remPB : List ChainEpochPB) (sp0_val : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode)
    (hsplit_len : convEpochs.length + 1 + remPB.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (dropProgAtExt b ext).fnAddr chainFromPbName + 944#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hx19 : s.readReg64 .x19 = 0#64) (hx21 : s.readReg64 .x21 = x.gPb.nextRoot.cap)
    (hx22 : s.readReg64 .x22 = x.gPb.nextRoot.ptr) (hx24 : s.readReg64 .x24 = x.out)
    (hx25 : s.readReg64 .x25 = x.gPb.linksCap) (hx26 : s.readReg64 .x26 = x.gPb.linksPtr)
    (hx27 : s.readReg64 .x27 = 0#64) :
    SepWP (dropProgAtExt b ext) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ memRegion x.pbPtr 80 ∗
        memRegion x.gPb.linksPtr (convEpochs.length * 112) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remPB.length * 112) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecCapPtrDealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗ A.pool ∗
        joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  have hep_ret := @fromPb_epilogue_ret A b ext x s0
  have hep_dealloc := @fromPb_epilogue_dealloc A b ext hdealloc x s0
  have hchain_slice : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr chainFromPbName + bv% (2 ^ 64 - ls_rel% "core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#2]" "<spqr::chain::Chain>::from_pb"))
      (dropChainEpochSliceSpec A) :=
    sub_ok_of_addr_eq (dropChainEpochSliceLocal2_rel_fromPb b ext)
      (drop_chain_epoch_slice_local2_ok_ext hdealloc)
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr chainFromPbName + bv% (ls_rel% "<spqr::chain::Chain>::from_pb" "__rustc::__rust_dealloc")) (rustDeallocSpec A) :=
    sub_ok_of_addr_eq (rustDealloc_rel_fromPb b ext) hdealloc
  have hlen_lt : x.pb.links.length * 112 < 2 ^ 63 :=
    lt_of_le_of_lt (Nat.mul_le_mul_right 112 hl_le) hl_lt
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  code_fetches_sym libsignalSessionCode libsignalSessionBin b (Rust.withPanics ext) "<spqr::chain::Chain>::from_pb" 1184
  dsimp only [dropProgAtExt, chainFromPbName, dropChainEpochSliceSpec,
    chainEpochSize, BitVec.ofNat_eq_ofNat] at hep_ret hep_dealloc hchain_slice hdealloc_raw hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::chain::Chain>::from_pb" = entry
  examples_hide_fetches
  refine seq_clean (mid := entry + 956#64)
    (P_mid := memRegion x.out 88 ∗ memRegion x.pbPtr 80 ∗
      memRegion x.gPb.linksPtr (convEpochs.length * 112) ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remPB.length * 112) ∗
      linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecCapPtrDealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗ A.pool ∗
      joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
      sm.readReg64 .x24 = x.out ∧ sm.readReg64 .x25 = x.gPb.linksCap ∧
      sm.readReg64 .x26 = x.gPb.linksPtr ∧ sm.readReg64 .x27 = 0#64) ?_ ?_
  · refine SepWP.focus_weaken
      (pool_entails_empty_arrayAt_pool A (chainEpoch A) 112 x.gPb.linksPtr) (by sep_focus) ?_
    rw [stackAt_subStack_split_dropStack32 s0.sp]
    wp_steps
    wp_call hchain_slice ⟨x.gPb.linksPtr, []⟩
    rw [hsp, memRegion_zero, emp_sepConj]; wp_done
  · rintro s3 hpc3 hrun3 ⟨hsp3, htr3, hx21_3, hx22_3, hx24_3, hx25_3, hx26_3, hx27_3⟩
    have hjoin3 :
        memRegion x.gPb.linksPtr (convEpochs.length * 112) ∗
          memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
          memRegion (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remPB.length * 112) ⊢
          memRegion x.gPb.linksPtr (x.pb.links.length * 112) := by
      rw [← hsplit_len]
      exact memRegion_join_three_112 x.gPb.linksPtr convEpochs.length remPB.length
        (by rw [hsplit_len]; exact hlen_lt)
    refine SepWP.focus_weaken hjoin3 (by sep_focus) ?_
    refine SepWP.focus_weaken
      (linksRawAllocAt_combine_memRegion A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length hl_le hl_lt)
      (by sep_focus) ?_
    refine seq_clean (mid := entry + 980#64)
      (P_mid := memRegion x.out 88 ∗ memRegion x.pbPtr 80 ∗
        vecCapPtrDealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗ A.pool ∗
        joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
        sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
        sm.readReg64 .x24 = x.out ∧ sm.readReg64 .x27 = 0#64) ?_ ?_
    · by_cases hc : x.gPb.linksCap = 0
      · have hcb : (x.gPb.linksCap == 0#64) = true := beq_iff_eq.mpr hc
        simp only [hcb, ↓reduceIte, emp_sepConj, sepConj_emp]; wp_steps; wp_done
      · have hcb : (x.gPb.linksCap == 0#64) = false := beq_eq_false_iff_ne.mpr hc
        have hpos : x.gPb.linksCap.toNat * 112 > 0 := by
          have : x.gPb.linksCap.toNat > 0 := Nat.pos_of_ne_zero (by
            intro hz; exact hc (BitVec.eq_of_toNat_eq (by simpa using hz)))
          omega
        have hlsl := cap_mul_112_shift_eq x.gPb.linksCap hl_lt
        simp only [hcb, Bool.false_eq_true, ↓reduceIte]
        rw [stackAt_subStack_split_allocHook s0.sp]
        wp_steps
        wp_call hdealloc_raw (x.gPb.linksPtr, x.gPb.linksCap.toNat * 112, 8)
        rw [hsp3]; wp_done
    · rintro s4 hpc4 hrun4 ⟨hsp4, htr4, hx21_4, hx22_4, hx24_4, hx27_4⟩
      rw [memRegion_88_words4_rest x.out]
      wp_pull_exists
      unfold vecCapPtrDealloc
      by_cases hnr : x.gPb.nextRoot.cap = 0
      · have hnrb : (x.gPb.nextRoot.cap == 0#64) = true := beq_iff_eq.mpr hnr
        simp only [hnrb, ↓reduceIte, emp_sepConj, sepConj_emp]
        refine seq_clean (mid := entry + 1140#64)
          (P_mid := chainResultAt A x.out (Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗ A.pool ∗
            memRegion (s0.sp - 192#64) 96 ∗ calleeSavedFromPbAt s0 ∗
            stackAt (s0.sp - 192#64) chainFromPbSubStack)
          (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0) ?_ ?_
        · unfold joinScratchAt; wp_steps
          refine SepWP.focus_weaken
            (err_stateDecode_pack_words A x.out x.pb hfromPb_eq 0#64 sp0_val _ rfl)
            (by sep_focus) ?_
          refine SepWP.focus_weaken
            (joinScratchAt_entails_memRegion_96 s0 x.gPb x.pb sp0_val)
            (by unfold joinScratchAt; sep_focus) ?_
          wp_done
        · rintro s5 hpc5 hrun5 ⟨hsp5, htr5⟩
          exact hep_ret s5 hsp0_align hpc5 hrun5 hsp5 htr5
      · have hnrb : (x.gPb.nextRoot.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hnr
        simp only [hnrb, Bool.false_eq_true, ↓reduceIte]
        refine seq_clean (mid := entry + 1008#64)
          (P_mid := chainResultAt A x.out (Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗ A.pool ∗
            A.live x.gPb.nextRoot.ptr x.gPb.nextRoot.cap.toNat 1 ∗
            memRegion x.gPb.nextRoot.ptr x.gPb.nextRoot.cap.toNat ∗
            memRegion (s0.sp - 192#64) 96 ∗ calleeSavedFromPbAt s0 ∗
            stackAt (s0.sp - 192#64) chainFromPbSubStack)
          (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
            sm.readReg64 .x0 = x.gPb.nextRoot.ptr ∧ sm.readReg64 .x1 = x.gPb.nextRoot.cap) ?_ ?_
        · unfold joinScratchAt; wp_steps
          refine SepWP.focus_weaken
            (err_stateDecode_pack_words A x.out x.pb hfromPb_eq 0#64 sp0_val _ rfl)
            (by sep_focus) ?_
          refine SepWP.focus_weaken
            (joinScratchAt_entails_memRegion_96 s0 x.gPb x.pb sp0_val)
            (by unfold joinScratchAt; sep_focus) ?_
          wp_done
        · rintro s5 hpc5 hrun5 ⟨hsp5, htr5, hx0_5, hx1_5⟩
          exact hep_dealloc s5 x.gPb.nextRoot.cap x.gPb.nextRoot.ptr
            hsp0_align hnr hn_lt hn_ne hpc5 hrun5 hsp5 htr5 hx0_5 hx1_5

set_option maxHeartbeats 800000 in
theorem fromPb_join_err_840 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (x : ChainFromPbCall) (s0 s : State)
    (convEpochs : List ChainEpoch) (remPB : List ChainEpochPB) (sp0_val : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode)
    (hsplit_len : convEpochs.length + 1 + remPB.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (dropProgAtExt b ext).fnAddr chainFromPbName + 840#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64) (hx19 : s.readReg64 .x19 = 0#64)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 convEpochs.length)
    (hx21 : s.readReg64 .x21 = x.gPb.nextRoot.cap) (hx22 : s.readReg64 .x22 = x.gPb.nextRoot.ptr)
    (hx23 : s.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (hx24 : s.readReg64 .x24 = x.out) (hx26 : s.readReg64 .x26 = x.gPb.linksPtr)
    (hx27 : s.readReg64 .x27 = 0#64) :
    SepWP (dropProgAtExt b ext) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ memRegion x.pbPtr 80 ∗
        arrayAt (chainEpoch A) 112 x.gPb.linksPtr convEpochs ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remPB.length * 112) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecCapPtrDealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗ A.pool ∗
        joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  have htail := @fromPb_join_err_tail A b ext hdealloc x s0
  have hchain_slice : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr chainFromPbName + bv% (2 ^ 64 - ls_rel% "core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#2]" "<spqr::chain::Chain>::from_pb"))
      (dropChainEpochSliceSpec A) :=
    sub_ok_of_addr_eq (dropChainEpochSliceLocal2_rel_fromPb b ext)
      (drop_chain_epoch_slice_local2_ok_ext hdealloc)
  have hlen_lt : x.pb.links.length * 112 < 2 ^ 63 :=
    lt_of_le_of_lt (Nat.mul_le_mul_right 112 hl_le) hl_lt
  have hconv_lt : convEpochs.length * 112 < 2 ^ 63 := by
    have : convEpochs.length ≤ x.pb.links.length := by omega
    exact lt_of_le_of_lt (Nat.mul_le_mul_right 112 this) hlen_lt
  have hconv_le_cap : convEpochs.length ≤ x.gPb.linksCap.toNat := by omega
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  have hcsel1 := csel_sub_zero_of_le convEpochs.length x.gPb.linksCap hconv_le_cap
  have hcsel1_ult := csel_ult_sub_zero_of_le convEpochs.length x.gPb.linksCap hconv_le_cap
  have hcsel2 := csel_min_eq_of_le convEpochs.length x.gPb.linksCap hconv_le_cap
  have hcsel2_ult := csel_ult_min_eq_of_le convEpochs.length x.gPb.linksCap hconv_le_cap
  have hcsel3 := csel_zero_if_ptr_eq x.gPb.linksPtr convEpochs.length hconv_lt
  have hcsel3_eq := csel_eq_zero_if_ptr_eq x.gPb.linksPtr convEpochs.length hconv_lt
  code_fetches_sym libsignalSessionCode libsignalSessionBin b (Rust.withPanics ext) "<spqr::chain::Chain>::from_pb" 1184
  dsimp only [dropProgAtExt, chainFromPbName, dropChainEpochSliceSpec,
    chainEpochSize, BitVec.ofNat_eq_ofNat] at htail hchain_slice hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::chain::Chain>::from_pb" = entry
  examples_hide_fetches
  refine seq_clean (mid := entry + 944#64)
    (P_mid := memRegion x.out 88 ∗ memRegion x.pbPtr 80 ∗
      memRegion x.gPb.linksPtr (convEpochs.length * 112) ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remPB.length * 112) ∗
      linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecCapPtrDealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗ A.pool ∗
      joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .x19 = 0#64 ∧ sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧
      sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧ sm.readReg64 .x24 = x.out ∧
      sm.readReg64 .x25 = x.gPb.linksCap ∧ sm.readReg64 .x26 = x.gPb.linksPtr ∧
      sm.readReg64 .x27 = 0#64) ?_ ?_
  · unfold joinScratchAt
    rw [stackAt_subStack_split_dropStack32 s0.sp]
    wp_steps
    wp_call hchain_slice ⟨x.gPb.linksPtr, convEpochs⟩
    rw [hsp]; wp_done
  · rintro s2 hpc2 hrun2 ⟨hsp2, htr2, hx19_2, hx21_2, hx22_2, hx24_2, hx25_2, hx26_2, hx27_2⟩
    exact htail s2 convEpochs remPB sp0_val hsp0_align hfromPb_eq hsplit_len hl_le hl_lt hn_lt hn_ne
      hpc2 hrun2 hsp2 htr2 hx19_2 hx21_2 hx22_2 hx24_2 hx25_2 hx26_2 hx27_2

set_option maxHeartbeats 800000 in
theorem fromPb_join_err {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (x : ChainFromPbCall) (s0 s : State)
    (convG : List ChainEpochGhost) (convEpochs : List ChainEpoch)
    (remG : List ChainEpochPBGhost) (remPB : List ChainEpochPB) (sp0_val : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode)
    (hconv_len : convG.length = convEpochs.length) (hrem_len : remG.length = remPB.length)
    (hsplit_len : convEpochs.length + 1 + remPB.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (_hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (dropProgAtExt b ext).fnAddr chainFromPbName + 792#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hx29 : s.readReg64 .fp = s0.sp - 96#64)
    (hx0 : s.readReg64 .x0 = x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112))
    (hx11 : s.readReg64 .x11 = x.gPb.linksPtr) (hx19 : s.readReg64 .x19 = 0#64)
    (hx20 : s.readReg64 .x20 = x.gPb.linksPtr + BitVec.ofNat 64 (x.pb.links.length * 112))
    (hx21 : s.readReg64 .x21 = x.gPb.nextRoot.cap) (hx22 : s.readReg64 .x22 = x.gPb.nextRoot.ptr)
    (hx23 : s.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (hx24 : s.readReg64 .x24 = x.out) (hx27 : s.readReg64 .x27 = 0#64) :
    SepWP (dropProgAtExt b ext) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        arrayAt (chainEpochPBAt A) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  have h840 := @fromPb_join_err_840 A b ext hdealloc x s0
  have hproto_slice : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr chainFromPbName + bv% (2 ^ 64 - ls_rel% "core::ptr::drop_glue::<[spqr::proto::pq_ratchet::chain::Epoch]>" "<spqr::chain::Chain>::from_pb"))
      (dropProtoEpochSliceSpec A) :=
    sub_ok_of_addr_eq (dropProtoEpochSlice_rel_fromPb b ext) (drop_proto_epoch_slice_ok_ext hdealloc)
  have hlen_lt : x.pb.links.length * 112 < 2 ^ 63 :=
    lt_of_le_of_lt (Nat.mul_le_mul_right 112 hl_le) hl_lt
  have hrem_lt : remPB.length * 112 < 2 ^ 63 := by
    have : remPB.length ≤ x.pb.links.length := by omega
    exact lt_of_le_of_lt (Nat.mul_le_mul_right 112 this) hlen_lt
  have hconv_lt : convEpochs.length * 112 < 2 ^ 63 := by
    have : convEpochs.length ≤ x.pb.links.length := by omega
    exact lt_of_le_of_lt (Nat.mul_le_mul_right 112 this) hlen_lt
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  have hsub_rem := sub_links_rem_112 x.gPb.linksPtr convEpochs.length remPB.length
    x.pb.links.length hsplit_len
  have hsub_conv := sub_links_conv_112 x.gPb.linksPtr convEpochs.length
  have hdiv_rem := div_112_magic_eq hrem_lt
  have hdiv_rem_nat := div_112_magic_nat_eq hrem_lt
  have hdiv_conv := div_112_magic_eq hconv_lt
  have hdiv_conv_nat := div_112_magic_nat_eq hconv_lt
  refine SepWP.focus_weaken
    (arrayAt_chainEpochPBAt_entails_protoRepr A remG remPB
      (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) hrem_len)
    (by sep_focus) ?_
  refine SepWP.focus_weaken
    (arrayAt_chainEpochAt_entails_unpinned A convG convEpochs x.gPb.linksPtr hconv_len)
    (by sep_focus) ?_
  refine SepWP.focus_weaken
    (vecU8BufAt_entails_dealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot hn_le hn_lt)
    (by sep_focus) ?_
  refine SepWP.focus_weaken
    (chainPBHeadersAt_entails_memRegion_80 x.pbPtr x.gPb x.pb) (by sep_focus) ?_
  code_fetches_sym libsignalSessionCode libsignalSessionBin b (Rust.withPanics ext) "<spqr::chain::Chain>::from_pb" 1184
  dsimp only [dropProgAtExt, chainFromPbName, dropProtoEpochSliceSpec,
    ProtoRepr.chainEpochPBSize, BitVec.ofNat_eq_ofNat] at h840 hproto_slice hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::chain::Chain>::from_pb" = entry
  examples_hide_fetches
  refine seq_clean (mid := entry + 840#64)
    (P_mid := memRegion x.out 88 ∗ memRegion x.pbPtr 80 ∗
      arrayAt (chainEpoch A) 112 x.gPb.linksPtr convEpochs ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remPB.length * 112) ∗
      linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecCapPtrDealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗ A.pool ∗
      joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x19 = 0#64 ∧
      sm.readReg64 .x20 = BitVec.ofNat 64 convEpochs.length ∧
      sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
      sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
      sm.readReg64 .x24 = x.out ∧ sm.readReg64 .x26 = x.gPb.linksPtr ∧
      sm.readReg64 .x27 = 0#64) ?_ ?_
  · rw [stackAt_subStack_split_dropStack32 s0.sp]
    wp_steps
    wp_call hproto_slice ⟨x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112), remPB⟩
    rw [hsp]; wp_done
  · rintro s1 hpc1 hrun1 ⟨hsp1, htr1, hfp1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx26_1, hx27_1⟩
    exact h840 s1 convEpochs remPB sp0_val hsp0_align hfromPb_eq hsplit_len hl_le hl_lt hn_lt hn_ne
      hpc1 hrun1 hsp1 htr1 hfp1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx26_1 hx27_1

/-! ## Join-Point Success Path `fromPb_join_ok` (`0x6038c .. 0x60504`, `w19 = 1`) -/

set_option maxHeartbeats 800000 in
theorem fromPb_join_params_none_tail {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (x : ChainFromPbCall) (s0 s : State)
    (convEpochs : List ChainEpoch) (sp0_val : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpb_len : convEpochs.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (dropProgAtExt b ext).fnAddr chainFromPbName + 1100#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hx19 : s.readReg64 .x19 = 0#64) (hx20 : s.readReg64 .x20 = x.gPb.linksPtr)
    (hx21 : s.readReg64 .x21 = x.gPb.nextRoot.cap) (hx22 : s.readReg64 .x22 = x.gPb.nextRoot.ptr)
    (hx25 : s.readReg64 .x25 = x.gPb.linksCap) :
    SepWP (dropProgAtExt b ext) (s0.readReg64 .lr) s
      (chainResultAt A x.out (Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗
        memRegion x.gPb.linksPtr (convEpochs.length * 112) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecCapPtrDealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗ A.pool ∗
        joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  have hep_ret := @fromPb_epilogue_ret A b ext x s0
  have hep_dealloc := @fromPb_epilogue_dealloc A b ext hdealloc x s0
  have hchain_slice : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr chainFromPbName + bv% (2 ^ 64 - ls_rel% "core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#2]" "<spqr::chain::Chain>::from_pb"))
      (dropChainEpochSliceSpec A) :=
    sub_ok_of_addr_eq (dropChainEpochSliceLocal2_rel_fromPb b ext)
      (drop_chain_epoch_slice_local2_ok_ext hdealloc)
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr chainFromPbName + bv% (ls_rel% "<spqr::chain::Chain>::from_pb" "__rustc::__rust_dealloc")) (rustDeallocSpec A) :=
    sub_ok_of_addr_eq (rustDealloc_rel_fromPb b ext) hdealloc
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  code_fetches_sym libsignalSessionCode libsignalSessionBin b (Rust.withPanics ext) "<spqr::chain::Chain>::from_pb" 1184
  dsimp only [dropProgAtExt, chainFromPbName, dropChainEpochSliceSpec,
    chainEpochSize, BitVec.ofNat_eq_ofNat] at hep_ret hep_dealloc hchain_slice hdealloc_raw hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::chain::Chain>::from_pb" = entry
  examples_hide_fetches
  refine seq_clean (mid := entry + 1112#64)
    (P_mid := chainResultAt A x.out (Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗
      memRegion x.gPb.linksPtr (convEpochs.length * 112) ∗
      linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecCapPtrDealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗ A.pool ∗
      joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .x20 = x.gPb.linksPtr ∧ sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧
      sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧ sm.readReg64 .x25 = x.gPb.linksCap) ?_ ?_
  · refine SepWP.focus_weaken
      (pool_entails_empty_arrayAt_pool A (chainEpoch A) 112 x.gPb.linksPtr) (by sep_focus) ?_
    rw [stackAt_subStack_split_dropStack32 s0.sp]
    wp_steps
    wp_call hchain_slice ⟨x.gPb.linksPtr, []⟩
    rw [hsp, memRegion_zero, emp_sepConj]; wp_done
  · rintro s3 hpc3 hrun3 ⟨hsp3, htr3, hx20_3, hx21_3, hx22_3, hx25_3⟩
    rw [hpb_len]
    refine SepWP.focus_weaken
      (linksRawAllocAt_combine_memRegion A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length hl_le hl_lt)
      (by sep_focus) ?_
    refine seq_clean (mid := entry + 1136#64)
      (P_mid := chainResultAt A x.out (Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗
        vecCapPtrDealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗ A.pool ∗
        joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
        sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr) ?_ ?_
    · by_cases hc : x.gPb.linksCap = 0
      · have hcb : (x.gPb.linksCap == 0#64) = true := beq_iff_eq.mpr hc
        simp only [hcb, ↓reduceIte, emp_sepConj, sepConj_emp]; wp_steps; wp_done
      · have hcb : (x.gPb.linksCap == 0#64) = false := beq_eq_false_iff_ne.mpr hc
        have hpos : x.gPb.linksCap.toNat * 112 > 0 := by
          have : x.gPb.linksCap.toNat > 0 := Nat.pos_of_ne_zero (by
            intro hz; exact hc (BitVec.eq_of_toNat_eq (by simpa using hz)))
          omega
        have hlsl := cap_mul_112_shift_eq x.gPb.linksCap hl_lt
        simp only [hcb, Bool.false_eq_true, ↓reduceIte]
        rw [stackAt_subStack_split_allocHook s0.sp]
        wp_steps
        wp_call hdealloc_raw (x.gPb.linksPtr, x.gPb.linksCap.toNat * 112, 8)
        rw [hsp3]; wp_done
    · rintro s4 hpc4 hrun4 ⟨hsp4, htr4, hx21_4, hx22_4⟩
      unfold vecCapPtrDealloc
      refine SepWP.focus_weaken
        (joinScratchAt_entails_memRegion_96 s0 x.gPb x.pb sp0_val) (by sep_focus) ?_
      by_cases hnr : x.gPb.nextRoot.cap = 0
      · have hnrb : (x.gPb.nextRoot.cap == 0#64) = true := beq_iff_eq.mpr hnr
        simp only [hnrb, ↓reduceIte, emp_sepConj, sepConj_emp]
        refine seq_clean (mid := entry + 1140#64)
          (P_mid := chainResultAt A x.out (Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗ A.pool ∗
            memRegion (s0.sp - 192#64) 96 ∗ calleeSavedFromPbAt s0 ∗
            stackAt (s0.sp - 192#64) chainFromPbSubStack)
          (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0) ?_ ?_
        · wp_steps; wp_done
        · rintro s5 hpc5 hrun5 ⟨hsp5, htr5⟩
          exact hep_ret s5 hsp0_align hpc5 hrun5 hsp5 htr5
      · have hnrb : (x.gPb.nextRoot.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hnr
        simp only [hnrb, Bool.false_eq_true, ↓reduceIte]
        refine seq_clean (mid := entry + 1008#64)
          (P_mid := chainResultAt A x.out (Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗ A.pool ∗
            A.live x.gPb.nextRoot.ptr x.gPb.nextRoot.cap.toNat 1 ∗
            memRegion x.gPb.nextRoot.ptr x.gPb.nextRoot.cap.toNat ∗
            memRegion (s0.sp - 192#64) 96 ∗ calleeSavedFromPbAt s0 ∗
            stackAt (s0.sp - 192#64) chainFromPbSubStack)
          (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
            sm.readReg64 .x0 = x.gPb.nextRoot.ptr ∧ sm.readReg64 .x1 = x.gPb.nextRoot.cap) ?_ ?_
        · wp_steps; wp_done
        · rintro s5 hpc5 hrun5 ⟨hsp5, htr5, hx0_5, hx1_5⟩
          exact hep_dealloc s5 x.gPb.nextRoot.cap x.gPb.nextRoot.ptr
            hsp0_align hnr hn_lt hn_ne hpc5 hrun5 hsp5 htr5 hx0_5 hx1_5

set_option maxHeartbeats 800000 in
theorem fromPb_join_ok_840 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (x : ChainFromPbCall) (s0 s : State) (dir : Direction)
    (convG : List ChainEpochGhost) (convEpochs : List ChainEpoch) (sp0_val : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hdir : Direction.fromI32? x.pb.direction = some dir) (hdir_i32 : dir.toI32 = x.pb.direction)
    (hlinks : Chain.linksFromPb x.pb.links = .ok convEpochs)
    (hconv_len : convG.length = convEpochs.length) (hpb_len : convEpochs.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (dropProgAtExt b ext).fnAddr chainFromPbName + 840#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64) (hx19 : s.readReg64 .x19 = 1#64)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 convEpochs.length)
    (hx21 : s.readReg64 .x21 = x.gPb.nextRoot.cap) (hx22 : s.readReg64 .x22 = x.gPb.nextRoot.ptr)
    (hx23 : s.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (hx24 : s.readReg64 .x24 = x.out) (hx25 : s.readReg64 .x25 = x.pbPtr) :
    SepWP (dropProgAtExt b ext) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  have hep_ret := @fromPb_epilogue_ret A b ext x s0
  have hnone_tail := @fromPb_join_params_none_tail A b ext hdealloc x s0
  have hchain_slice : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr chainFromPbName + bv% (2 ^ 64 - ls_rel% "core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#2]" "<spqr::chain::Chain>::from_pb"))
      (dropChainEpochSliceSpec A) :=
    sub_ok_of_addr_eq (dropChainEpochSliceLocal2_rel_fromPb b ext)
      (drop_chain_epoch_slice_local2_ok_ext hdealloc)
  have hlen_lt : x.pb.links.length * 112 < 2 ^ 63 :=
    lt_of_le_of_lt (Nat.mul_le_mul_right 112 hl_le) hl_lt
  have hconv_lt : convEpochs.length * 112 < 2 ^ 63 := by rw [hpb_len]; exact hlen_lt
  have hconv_le_cap : convEpochs.length ≤ x.gPb.linksCap.toNat := by rw [hpb_len]; exact hl_le
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  code_fetches_sym libsignalSessionCode libsignalSessionBin b (Rust.withPanics ext) "<spqr::chain::Chain>::from_pb" 1184
  dsimp only [dropProgAtExt, chainFromPbName, dropChainEpochSliceSpec,
    chainEpochSize, BitVec.ofNat_eq_ofNat] at hep_ret hnone_tail hchain_slice hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::chain::Chain>::from_pb" = entry
  examples_hide_fetches
  cases hp : x.pb.params with
  | some cp =>
    have hfromPb_eq : Chain.fromPb x.pb = .ok {
        dir := dir, currentEpoch := x.pb.currentEpoch, sendEpoch := x.pb.sendEpoch,
        nextRoot := x.pb.nextRoot, links := convEpochs, params := cp } :=
      chainFromPb_of_ok hdir hlinks hp
    rw [memRegion_88_words4_rest x.out, memRegion_56_split_chainTail x.out]
    wp_pull_exists
    refine seq_clean (mid := entry + 1140#64)
      (P_mid := chainResultAt A x.out (Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗ A.pool ∗
        memRegion (s0.sp - 192#64) 96 ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0) ?_ ?_
    · unfold chainPBHeadersAt optChainParamsPBAt joinScratchAt
      rw [hp]; dsimp only
      wp_steps
      have hhdr :
          (x.pbPtr ↦₆₄ x.gPb.linksCap) ∗ ((x.pbPtr + 8#64) ↦₆₄ x.gPb.linksPtr) ∗
            ((x.pbPtr + 16#64) ↦₆₄ BitVec.ofNat 64 x.pb.links.length) ∗
            ((x.pbPtr + 24#64) ↦₆₄ x.gPb.nextRoot.cap) ∗ ((x.pbPtr + 32#64) ↦₆₄ x.gPb.nextRoot.ptr) ∗
            ((x.pbPtr + 40#64) ↦₆₄ BitVec.ofNat 64 x.pb.nextRoot.length) ∗
            ((x.pbPtr + 48#64) ↦₆₄ x.pb.currentEpoch) ∗ ((x.pbPtr + 56#64) ↦₆₄ x.pb.sendEpoch) ∗
            (((x.pbPtr + 64#64) ↦₃₂ 1#32) ∗ ((x.pbPtr + 64#64 + 4#64) ↦₃₂ cp.maxJump) ∗
              ((x.pbPtr + 64#64 + 8#64) ↦₃₂ cp.maxOooKeys)) ∗
            ((x.pbPtr + 76#64) ↦₃₂ x.pb.direction) ⊢ memRegion x.pbPtr 80 := by
        have := chainPBHeadersAt_entails_memRegion_80 x.pbPtr x.gPb x.pb
        unfold chainPBHeadersAt optChainParamsPBAt at this; rw [hp] at this; exact this
      refine SepWP.focus_weaken hhdr (by sep_focus) ?_
      have hpack :
          (x.out ↦₆₄ x.gPb.linksCap) ∗ ((x.out + 8#64) ↦₆₄ x.gPb.linksPtr) ∗
            ((x.out + 16#64) ↦₆₄ 0#64) ∗ ((x.out + 24#64) ↦₆₄ BitVec.ofNat 64 x.pb.links.length) ∗
            ((x.out + 32#64) ↦₆₄ x.gPb.nextRoot.cap) ∗ ((x.out + 40#64) ↦₆₄ x.gPb.nextRoot.ptr) ∗
            ((x.out + 48#64) ↦₆₄ BitVec.ofNat 64 x.pb.nextRoot.length) ∗
            ((x.out + 56#64) ↦₆₄ x.pb.currentEpoch) ∗ ((x.out + 64#64) ↦₆₄ x.pb.sendEpoch) ∗
            ((x.out + 72#64) ↦₃₂ cp.maxJump) ∗ ((x.out + 76#64) ↦₃₂ cp.maxOooKeys) ∗
            ((x.out + 80#64) ↦₃₂ x.pb.direction) ∗ memRegion (x.out + 84#64) 4 ∗
            arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
            linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
            vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ⊢
            chainResultAt A x.out (Chain.fromPb x.pb) := by
        rw [hfromPb_eq, ← hdir_i32, ← hpb_len]
        exact chainResultAt_ok_pack A x.out x.gPb.linksCap x.gPb.linksPtr
          x.gPb.nextRoot.cap x.gPb.nextRoot.ptr convG convEpochs x.pb.nextRoot
          x.pb.currentEpoch x.pb.sendEpoch cp dir
          hconv_len hconv_le_cap hl_lt hl_ne hn_le hn_lt hn_ne
      refine SepWP.focus_weaken hpack (by sep_focus) ?_
      refine SepWP.focus_weaken
        (joinScratchAt_entails_memRegion_96 s0 x.gPb x.pb sp0_val)
        (by unfold joinScratchAt; sep_focus) ?_
      wp_done
    · rintro s2 hpc2 hrun2 ⟨hsp2, htr2⟩
      exact hep_ret s2 hsp0_align hpc2 hrun2 hsp2 htr2
  | none =>
    have hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode :=
      chainFromPb_of_params_none hdir hlinks hp
    have hcsel1 := csel_sub_zero_of_le convEpochs.length x.gPb.linksCap hconv_le_cap
    have hcsel1_ult := csel_ult_sub_zero_of_le convEpochs.length x.gPb.linksCap hconv_le_cap
    have hcsel2 := csel_min_eq_of_le convEpochs.length x.gPb.linksCap hconv_le_cap
    have hcsel2_ult := csel_ult_min_eq_of_le convEpochs.length x.gPb.linksCap hconv_le_cap
    have hcsel3 := csel_zero_if_ptr_eq x.gPb.linksPtr convEpochs.length hconv_lt
    have hcsel3_eq := csel_eq_zero_if_ptr_eq x.gPb.linksPtr convEpochs.length hconv_lt
    have hcsel1_pb := csel_sub_zero_of_le x.pb.links.length x.gPb.linksCap hl_le
    have hcsel1_ult_pb := csel_ult_sub_zero_of_le x.pb.links.length x.gPb.linksCap hl_le
    have hcsel2_pb := csel_min_eq_of_le x.pb.links.length x.gPb.linksCap hl_le
    have hcsel2_ult_pb := csel_ult_min_eq_of_le x.pb.links.length x.gPb.linksCap hl_le
    have hcsel3_pb := csel_zero_if_ptr_eq x.gPb.linksPtr x.pb.links.length hlen_lt
    have hcsel3_eq_pb := csel_eq_zero_if_ptr_eq x.gPb.linksPtr x.pb.links.length hlen_lt
    refine SepWP.focus_weaken
      (arrayAt_chainEpochAt_entails_unpinned A convG convEpochs x.gPb.linksPtr hconv_len)
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (vecU8BufAt_entails_dealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot hn_le hn_lt)
      (by sep_focus) ?_
    refine seq_clean (mid := entry + 1044#64)
      (P_mid := memRegion x.out 88 ∗ memRegion x.pbPtr 80 ∗
        arrayAt (chainEpoch A) 112 x.gPb.linksPtr convEpochs ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecCapPtrDealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗ A.pool ∗
        joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
        sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x20 = BitVec.ofNat 64 convEpochs.length ∧
        sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
        sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
        sm.readReg64 .x24 = x.out) ?_ ?_
    · unfold chainPBHeadersAt optChainParamsPBAt
      rw [hp]; dsimp only
      wp_steps
      have hhdr :
          (x.pbPtr ↦₆₄ x.gPb.linksCap) ∗ ((x.pbPtr + 8#64) ↦₆₄ x.gPb.linksPtr) ∗
            ((x.pbPtr + 16#64) ↦₆₄ BitVec.ofNat 64 x.pb.links.length) ∗
            ((x.pbPtr + 24#64) ↦₆₄ x.gPb.nextRoot.cap) ∗ ((x.pbPtr + 32#64) ↦₆₄ x.gPb.nextRoot.ptr) ∗
            ((x.pbPtr + 40#64) ↦₆₄ BitVec.ofNat 64 x.pb.nextRoot.length) ∗
            ((x.pbPtr + 48#64) ↦₆₄ x.pb.currentEpoch) ∗ ((x.pbPtr + 56#64) ↦₆₄ x.pb.sendEpoch) ∗
            (((x.pbPtr + 64#64) ↦₃₂ 0#32) ∗ memRegion (x.pbPtr + 64#64 + 4#64) 8) ∗
            ((x.pbPtr + 76#64) ↦₃₂ x.pb.direction) ⊢ memRegion x.pbPtr 80 := by
        have := chainPBHeadersAt_entails_memRegion_80 x.pbPtr x.gPb x.pb
        unfold chainPBHeadersAt optChainParamsPBAt at this; rw [hp] at this; exact this
      refine SepWP.focus_weaken hhdr (by sep_focus) ?_
      wp_done
    · rintro s1 hpc1 hrun1 ⟨hsp1, htr1, hfp1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1⟩
      rw [memRegion_88_words4_rest x.out]
      wp_pull_exists
      refine seq_clean (mid := entry + 1100#64)
        (P_mid := chainResultAt A x.out (Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗
          memRegion x.gPb.linksPtr (convEpochs.length * 112) ∗
          linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
          vecCapPtrDealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗ A.pool ∗
          joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
          stackAt (s0.sp - 192#64) chainFromPbSubStack)
        (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
          sm.readReg64 .x19 = 0#64 ∧ sm.readReg64 .x20 = x.gPb.linksPtr ∧
          sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
          sm.readReg64 .x25 = x.gPb.linksCap) ?_ ?_
      · unfold joinScratchAt
        rw [stackAt_subStack_split_dropStack32 s0.sp]
        wp_steps
        refine SepWP.focus_weaken
          (err_stateDecode_pack_words A x.out x.pb hfromPb_eq _ _ _ (bitvec_low_byte_clear_zero _))
          (by sep_focus) ?_
        wp_call hchain_slice ⟨x.gPb.linksPtr, convEpochs⟩
        rw [hsp1]; wp_done
      · rintro s2 hpc2 hrun2 ⟨hsp2, htr2, hx19_2, hx20_2, hx21_2, hx22_2, hx25_2⟩
        exact hnone_tail s2 convEpochs sp0_val hsp0_align hpb_len hl_le hl_lt hn_lt hn_ne
          hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx25_2

set_option maxHeartbeats 800000 in
theorem fromPb_join_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (x : ChainFromPbCall) (s0 s : State) (dir : Direction)
    (convG : List ChainEpochGhost) (convEpochs : List ChainEpoch) (sp0_val : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hdir : Direction.fromI32? x.pb.direction = some dir) (hdir_i32 : dir.toI32 = x.pb.direction)
    (hlinks : Chain.linksFromPb x.pb.links = .ok convEpochs)
    (hconv_len : convG.length = convEpochs.length) (hpb_len : convEpochs.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (dropProgAtExt b ext).fnAddr chainFromPbName + 792#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hx29 : s.readReg64 .fp = s0.sp - 96#64)
    (hx0 : s.readReg64 .x0 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (hx11 : s.readReg64 .x11 = x.gPb.linksPtr) (hx19 : s.readReg64 .x19 = 1#64)
    (hx20 : s.readReg64 .x20 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (hx21 : s.readReg64 .x21 = x.gPb.nextRoot.cap) (hx22 : s.readReg64 .x22 = x.gPb.nextRoot.ptr)
    (hx23 : s.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (hx24 : s.readReg64 .x24 = x.out) (hx25 : s.readReg64 .x25 = x.pbPtr) :
    SepWP (dropProgAtExt b ext) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  have h840 := @fromPb_join_ok_840 A b ext hdealloc x s0
  have hproto_slice : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr chainFromPbName + bv% (2 ^ 64 - ls_rel% "core::ptr::drop_glue::<[spqr::proto::pq_ratchet::chain::Epoch]>" "<spqr::chain::Chain>::from_pb"))
      (dropProtoEpochSliceSpec A) :=
    sub_ok_of_addr_eq (dropProtoEpochSlice_rel_fromPb b ext) (drop_proto_epoch_slice_ok_ext hdealloc)
  have hlen_lt : x.pb.links.length * 112 < 2 ^ 63 :=
    lt_of_le_of_lt (Nat.mul_le_mul_right 112 hl_le) hl_lt
  have hconv_lt : convEpochs.length * 112 < 2 ^ 63 := by rw [hpb_len]; exact hlen_lt
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  have hsub_conv := sub_links_conv_112 x.gPb.linksPtr convEpochs.length
  have hdiv_conv := div_112_magic_eq hconv_lt
  have hdiv_conv_nat := div_112_magic_nat_eq hconv_lt
  have hsub_pb := sub_links_conv_112 x.gPb.linksPtr x.pb.links.length
  have hdiv_pb := div_112_magic_eq hlen_lt
  have hdiv_pb_nat := div_112_magic_nat_eq hlen_lt
  code_fetches_sym libsignalSessionCode libsignalSessionBin b (Rust.withPanics ext) "<spqr::chain::Chain>::from_pb" 1184
  dsimp only [dropProgAtExt, chainFromPbName, dropProtoEpochSliceSpec,
    ProtoRepr.chainEpochPBSize, BitVec.ofNat_eq_ofNat] at h840 hproto_slice hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::chain::Chain>::from_pb" = entry
  examples_hide_fetches
  refine seq_clean (mid := entry + 840#64)
    (P_mid := memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
      arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
      linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
      joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x19 = 1#64 ∧
      sm.readReg64 .x20 = BitVec.ofNat 64 convEpochs.length ∧
      sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
      sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
      sm.readReg64 .x24 = x.out ∧ sm.readReg64 .x25 = x.pbPtr) ?_ ?_
  · refine SepWP.focus_weaken
      (pool_entails_empty_arrayAt_pool A (fun ep addr => ProtoRepr.chainEpochPBAt A addr ep) 112
        (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))) (by sep_focus) ?_
    rw [stackAt_subStack_split_dropStack32 s0.sp]
    wp_steps
    wp_call hproto_slice ⟨x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112), []⟩
    rw [hsp, memRegion_zero, emp_sepConj]; wp_done
  · rintro s1 hpc1 hrun1 ⟨hsp1, htr1, hfp1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1⟩
    exact h840 s1 dir convG convEpochs sp0_val hsp0_align hdir hdir_i32 hlinks hconv_len hpb_len
      hl_le hl_lt hl_ne hn_le hn_lt hn_ne hpc1 hrun1 hsp1 htr1 hfp1 hx19_1 hx20_1 hx21_1 hx22_1
      hx23_1 hx24_1 hx25_1

/-! ## Relocatable `[LibsignalPlacement]` Drop Glue (Blocks `287` & `338`) -/

section PlacedDropGlue

open CryptoVerification.SpqrV1.ProtoRepr

@[local simp]
private theorem optEpochDirectionPBAt_none_placed (A : RustAlloc) (a : BitVec 64) :
    optEpochDirectionPBAt A a none = ((a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 48) := rfl

@[local simp]
private theorem optEpochDirectionPBAt_some_placed (A : RustAlloc) (a : BitVec 64) (d : EpochDirectionPB) :
    optEpochDirectionPBAt A a (some d) = epochDirectionPBAt A a d := rfl

private theorem drop_chain_epoch_slice_local2_placed_body [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_287).rebase (blkPl_287).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (ep : ChainEpoch)
      (s : State) (Frame : SepProp),
      s.pc = (blkPl_287).base + 40#64 →
      s.status = .Running →
      Saved32x20Preserved s0 s fsp →
      s.readReg64 .x19 = cnt →
      s.readReg64 .x20 = cur + 56#64 →
      SepWP ((blkPC_287).rebase (blkPl_287).base H)
        ((blkPl_287).base + 28#64)
        s
        (chainEpoch A ep cur ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 112 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved32x20Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = cnt ∧
          sm.readReg64 .x20 = cur + 56#64) := by
  simp only [rustDeallocSpec] at hdealloc
  intro cur cnt ep s Frame hpc hrun hpres hx19 hx20
  rcases hpres with ⟨hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine SepWP.weaken_pre (sepConj_mono_left (chainEpoch_entails_dealloc A cur ep)) ?_
  apply SepWP.exists_sepConj_left; intro g
  refine seq_clean (mid := (blkPl_287).base + 60#64) (P_mid :=
    (chainEpochHeadersAt cur g ∗
      vecCapPtrDealloc A g.send.prev.cap g.send.prev.ptr ∗
      vecCapPtrDealloc A g.recv.next.cap g.recv.next.ptr ∗
      vecCapPtrDealloc A g.recv.prev.cap g.recv.prev.ptr) ∗
    A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => Saved32x20Preserved s0 sm fsp ∧
      sm.readReg64 .x19 = cnt ∧ sm.readReg64 .x20 = cur + 56#64)
    ?_ ?_
  · dsimp only [chainEpochHeadersAt, vecCapPtrDealloc]
    by_cases hcap : (g.send.next.cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; wp_done
    · wp_steps; wp_apply; refine align_pre (by rw [hsp]; ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx20_1⟩
    refine seq_clean (mid := (blkPl_287).base + 80#64) (P_mid :=
      (chainEpochHeadersAt cur g ∗
        vecCapPtrDealloc A g.recv.next.cap g.recv.next.ptr ∗
        vecCapPtrDealloc A g.recv.prev.cap g.recv.prev.ptr) ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q := fun sm => Saved32x20Preserved s0 sm fsp ∧
        sm.readReg64 .x19 = cnt ∧ sm.readReg64 .x20 = cur + 56#64)
      ?_ ?_
    · dsimp only [chainEpochHeadersAt, vecCapPtrDealloc]
      by_cases hcap : (g.send.prev.cap == 0#64) = true <;>
        simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; wp_done
      · wp_steps; wp_apply; refine align_pre (by rw [hsp_1]; ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2, hx20_2⟩
      refine seq_clean (mid := (blkPl_287).base + 100#64) (P_mid :=
        (chainEpochHeadersAt cur g ∗
          vecCapPtrDealloc A g.recv.prev.cap g.recv.prev.ptr) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (Q := fun sm => Saved32x20Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = cnt ∧ sm.readReg64 .x20 = cur + 56#64)
        ?_ ?_
      · dsimp only [chainEpochHeadersAt, vecCapPtrDealloc]
        by_cases hcap : (g.recv.next.cap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; wp_done
        · wp_steps; wp_apply; refine align_pre (by rw [hsp_2]; ac_rfl) ?_; wp_done
      · intro s3 hpc3 hrun3 ⟨⟨hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3, hx20_3⟩
        have hstep4 : SepWP ((blkPC_287).rebase (blkPl_287).base H) ((blkPl_287).base + 28#64) s3
            ((chainEpochHeadersAt cur g ∗ vecCapPtrDealloc A g.recv.prev.cap g.recv.prev.ptr) ∗
              A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
            (fun sm Pm =>
              (Pm ⊢ chainEpochHeadersAt cur g ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
              Saved32x20Preserved s0 sm fsp ∧
              sm.readReg64 .x19 = cnt ∧ sm.readReg64 .x20 = cur + 56#64) := by
          dsimp only [chainEpochHeadersAt, vecCapPtrDealloc]
          by_cases hcap : (g.recv.prev.cap == 0#64) = true <;>
            simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; wp_done
          · wp_steps; wp_apply; wp_steps; refine align_pre (by rw [hsp_3]; ac_rfl) ?_; wp_done
        exact SepWP.mono hstep4 (fun sm Pm _ _ h =>
          ⟨Entails.trans h.1 (sepConj_mono_left (chainEpochHeadersAt_entails_memRegion_112 cur g)), h.2⟩)

private theorem drop_chain_epoch_slice_local2_placed_loop [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_287).rebase (blkPl_287).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List ChainEpoch) (cur : BitVec 64)
      (s : State) (Frame : SepProp),
      rest ≠ [] →
      rest.length * 112 < 2 ^ 63 →
      s.pc = (blkPl_287).base + 40#64 →
      s.status = .Running →
      Saved32x20Preserved s0 s fsp →
      s.readReg64 .x19 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x20 = cur + 56#64 →
      SepWP ((blkPC_287).rebase (blkPl_287).base H)
        ((blkPl_287).base + 124#64)
        s
        (arrayAt (chainEpoch A) 112 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 112) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved32x20Preserved s0 sm fsp) := by
  have hbody := drop_chain_epoch_slice_local2_placed_body hdealloc s0 fsp hfsp_align
  intro rest
  induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons ep tl ih =>
    intro cur s Frame _ hlen hpc hrun hpres hx19 hx20
    rw [show arrayAt (chainEpoch A) 112 cur (ep :: tl) =
          chainEpoch A ep cur ∗ arrayAt (chainEpoch A) 112 (cur + 112#64) tl from rfl,
        sep_pull_body]
    refine seq_clean (mid := (blkPl_287).base + 28#64)
      (hbody cur (BitVec.ofNat 64 (ep :: tl).length) ep s
        (arrayAt (chainEpoch A) 112 (cur + 112#64) tl ∗ Frame)
        hpc hrun hpres hx19 hx20) ?_
    intro s4 hpc4 hrun4 ⟨⟨hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4, hx20_4⟩
    cases tl with
    | nil =>
      simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul,
        arrayAt, emp_sepConj] at hx19_4 ⊢
      wp_steps
      wp_done
    | cons ep2 tl2 =>
      have htl_ne : ep2 :: tl2 ≠ [] := List.cons_ne_nil _ _
      have htl_len := tail_len_mul_lt hlen
      rw [show (ep :: ep2 :: tl2).length = (ep2 :: tl2).length + 1 from rfl,
          ofNat_succ_eq_add_one] at hx19_4
      have hne1 := ofNat_add_one_beq_one_false_112 (n := (ep2 :: tl2).length) (by simp) htl_len
      wp_steps
      rw [sep_push_body]
      refine SepWP.mono
        (ih (cur + 112#64) _ (memRegion cur 112 ∗ Frame)
          htl_ne htl_len rfl (by assumption)
          ⟨hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩
          rfl
          (by simp only [wp_norm, arm64_norm, add_112_add_56])) ?_
      intro sf Pf _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2⟩
      have hsplit := cons_len_mul ep (ep2 :: tl2) 112
      have hbound : 112 + (ep2 :: tl2).length * 112 ≤ 2 ^ 64 := by
        rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
      rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 112 ((ep2 :: tl2).length * 112) hbound]
      exact Entails.refl _

/-- Relocatable `core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#2]` (Block `287`)
meets `dropChainEpochSliceSpec A` under `[LibsignalPlacement]`. -/
theorem drop_chain_epoch_slice_local2_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_287).rebase (blkPl_287).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_287).rebase (blkPl_287).base H)
      (blkPl_287).base (dropChainEpochSliceSpec A) := by
  simp only [dropChainEpochSliceSpec]
  have hloop := drop_chain_epoch_slice_local2_placed_loop hdealloc
  dsimp only [chainEpochSize, BitVec.ofNat_eq_ofNat] at hloop ⊢
  wp_init x s0
  rcases x with ⟨ptr, eps⟩
  have hx0 : s0.readReg64 .x0 = ptr := h_1
  have hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 eps.length := h_2
  have hlen_lt : eps.length * 112 < 2 ^ 63 := h
  dsimp only [DropChainEpochSliceGhost.ptr, DropChainEpochSliceGhost.eps] at *
  cases eps with
  | nil =>
    simp only [List.length_nil, Nat.zero_mul, arrayAt, memRegion_zero, emp_sepConj] at hx1 ⊢
    wp_steps
    wp_done
  | cons ep tl =>
    have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
      spAligned_sub s0.sp 32#64 (by assumption) (by decide)
    have hne0 := ofNat_beq_zero_false_112 (n := (ep :: tl).length) (by simp) hlen_lt
    nth_rw 1 [stackAt_dropStack32_split s0.sp]
    cells_unfold
    wp_pull_exists
    wp_steps
    refine seq_clean (mid := (blkPl_287).base + 124#64)
      (P_mid := memRegion ptr ((ep :: tl).length * 112) ∗ A.pool ∗
        stackAt (s0.sp - 32#64) allocHookStack ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (Q := fun sm => Saved32x20Preserved s0 sm (s0.sp - 32#64))
      ?_ ?_
    · have hpre_eq :
          (arrayAt (chainEpoch A) 112 ptr (ep :: tl) ∗
            A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) =
          (arrayAt (chainEpoch A) 112 ptr (ep :: tl) ∗
            A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) := by
        ac_rfl
      rw [hpre_eq]
      exact hloop s0 (s0.sp - 32#64) hfsp_align (ep :: tl) ptr _ _
        (List.cons_ne_nil _ _) hlen_lt rfl (by assumption)
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        rfl rfl
    · intro sm hpcm hrunm ⟨hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
      wp_steps
      refine SepWP.weaken_pre
        (sepConj_mono_right (sepConj_mono_right (stack_restore_32_allocHook s0.sp _ _ _ _))) ?_
      wp_done

private theorem drop_proto_epoch_slice_placed_body [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_288).rebase (blkPl_288).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (ep : ChainEpochPB)
      (s : State) (Frame : SepProp),
      s.pc = (blkPl_288).base + 40#64 →
      s.status = .Running →
      Saved32x20Preserved s0 s fsp →
      s.readReg64 .x19 = cnt →
      s.readReg64 .x20 = cur + 56#64 →
      SepWP ((blkPC_288).rebase (blkPl_288).base H)
        ((blkPl_288).base + 28#64)
        s
        (ProtoRepr.chainEpochPBAt A cur ep ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 112 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved32x20Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = cnt ∧
          sm.readReg64 .x20 = cur + 56#64) := by
  simp only [rustDeallocSpec] at hdealloc
  intro cur cnt ep s Frame hpc hrun hpres hx19 hx20
  rcases hpres with ⟨hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  unfold ProtoRepr.chainEpochPBAt
  refine seq_clean (mid := (blkPl_288).base + 88#64) (P_mid :=
    (memRegion cur 56 ∗ optEpochDirectionPBAt A (cur + 56#64) ep.recv) ∗
    A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => Saved32x20Preserved s0 sm fsp ∧
      sm.readReg64 .x19 = cnt ∧ sm.readReg64 .x20 = cur + 56#64)
    ?_ ?_
  · cases hsend : ep.send with
    | none =>
      rw [optEpochDirectionPBAt_none_placed]
      have hstep : SepWP ((blkPC_288).rebase (blkPl_288).base H) ((blkPl_288).base + 88#64) s
          (((cur ↦₆₄ noneCap ∗ memRegion (cur + 8#64) 48) ∗
            optEpochDirectionPBAt A (cur + 56#64) ep.recv) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ ((cur ↦₆₄ noneCap ∗ memRegion (cur + 8#64) 48) ∗
              optEpochDirectionPBAt A (cur + 56#64) ep.recv) ∗
              A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
            Saved32x20Preserved s0 sm fsp ∧
            sm.readReg64 .x19 = cnt ∧ sm.readReg64 .x20 = cur + 56#64) := by
        wp_steps; wp_done
      exact SepWP.strengthen_entails_const
        (sepConj_mono_left (sepConj_mono_left (optEpochDirectionPBAt_none_entails_memRegion_56 A cur)))
        hstep
    | some d =>
      rw [optEpochDirectionPBAt_some_placed]
      refine SepWP.weaken_pre
        (sepConj_mono_left (sepConj_mono_left (epochDirectionPBAt_entails_dealloc A cur d))) ?_
      rw [sepExists_sepConj_left, sepExists_sepConj_left]
      apply ProofLib.SepWP.exists_left; intro gs
      wp_focus_pure; intro hcap_lt_s
      have hne_none_s := cap_add_one_beq_zero_false hcap_lt_s
      refine seq_clean (mid := (blkPl_288).base + 68#64) (P_mid :=
        ((epochDirPBHeadersAt cur gs ∗ vecCapPtrDealloc A gs.prev.cap gs.prev.ptr) ∗
          optEpochDirectionPBAt A (cur + 56#64) ep.recv) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (Q := fun sm => Saved32x20Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = cnt ∧ sm.readReg64 .x20 = cur + 56#64)
        ?_ ?_
      · dsimp only [epochDirPBHeadersAt, vecCapPtrDealloc]
        by_cases hcap : (gs.next.cap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; wp_done
        · wp_steps; wp_apply; refine align_pre (by rw [hsp]; ac_rfl) ?_; wp_done
      · intro s1 hpc1 hrun1 ⟨⟨hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx20_1⟩
        have hstep2 : SepWP ((blkPC_288).rebase (blkPl_288).base H) ((blkPl_288).base + 88#64) s1
            (((epochDirPBHeadersAt cur gs ∗ vecCapPtrDealloc A gs.prev.cap gs.prev.ptr) ∗
              optEpochDirectionPBAt A (cur + 56#64) ep.recv) ∗
              A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
            (fun sm Pm =>
              (Pm ⊢ (epochDirPBHeadersAt cur gs ∗
                optEpochDirectionPBAt A (cur + 56#64) ep.recv) ∗
                A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
              Saved32x20Preserved s0 sm fsp ∧
              sm.readReg64 .x19 = cnt ∧ sm.readReg64 .x20 = cur + 56#64) := by
          dsimp only [epochDirPBHeadersAt, vecCapPtrDealloc]
          by_cases hcap : (gs.prev.cap == 0#64) = true <;>
            simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; wp_done
          · wp_steps; wp_apply; refine align_pre (by rw [hsp_1]; ac_rfl) ?_; wp_done
        exact SepWP.strengthen_entails_const
          (sepConj_mono_left (sepConj_mono_left (epochDirPBHeadersAt_entails_memRegion_56 cur gs)))
          hstep2
  · intro s2 hpc2 hrun2 ⟨⟨hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2, hx20_2⟩
    cases hrecv : ep.recv with
    | none =>
      rw [optEpochDirectionPBAt_none_placed]
      have hstep : SepWP ((blkPC_288).rebase (blkPl_288).base H) ((blkPl_288).base + 28#64) s2
          ((memRegion cur 56 ∗ ((cur + 56#64) ↦₆₄ noneCap ∗ memRegion ((cur + 56#64) + 8#64) 48)) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ (memRegion cur 56 ∗ ((cur + 56#64) ↦₆₄ noneCap ∗ memRegion ((cur + 56#64) + 8#64) 48)) ∗
              A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
            Saved32x20Preserved s0 sm fsp ∧
            sm.readReg64 .x19 = cnt ∧ sm.readReg64 .x20 = cur + 56#64) := by
        wp_steps; wp_done
      exact SepWP.strengthen_entails_const
        (sepConj_mono_left (Entails.trans
          (sepConj_mono_right (optEpochDirectionPBAt_none_entails_memRegion_56 A (cur + 56#64)))
          (chainEpochPB_regions_entails_112 cur)))
        hstep
    | some d =>
      rw [optEpochDirectionPBAt_some_placed]
      refine SepWP.weaken_pre
        (sepConj_mono_left (sepConj_mono_right (epochDirectionPBAt_entails_dealloc A (cur + 56#64) d))) ?_
      rw [sepExists_sepConj_right, sepExists_sepConj_left]
      apply ProofLib.SepWP.exists_left; intro gr
      wp_focus_pure; intro hcap_lt_r
      have hne_none_r := cap_add_one_beq_zero_false hcap_lt_r
      refine seq_clean (mid := (blkPl_288).base + 116#64) (P_mid :=
        (memRegion cur 56 ∗ (epochDirPBHeadersAt (cur + 56#64) gr ∗ vecCapPtrDealloc A gr.prev.cap gr.prev.ptr)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (Q := fun sm => Saved32x20Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = cnt ∧ sm.readReg64 .x20 = cur + 56#64)
        ?_ ?_
      · dsimp only [epochDirPBHeadersAt, vecCapPtrDealloc]
        by_cases hcap : (gr.next.cap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; wp_done
        · wp_steps; wp_apply; refine align_pre (by rw [hsp_2]; ac_rfl) ?_; wp_done
      · intro s3 hpc3 hrun3 ⟨⟨hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3, hx20_3⟩
        have hstep4 : SepWP ((blkPC_288).rebase (blkPl_288).base H) ((blkPl_288).base + 28#64) s3
            ((memRegion cur 56 ∗ (epochDirPBHeadersAt (cur + 56#64) gr ∗ vecCapPtrDealloc A gr.prev.cap gr.prev.ptr)) ∗
              A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
            (fun sm Pm =>
              (Pm ⊢ (memRegion cur 56 ∗ epochDirPBHeadersAt (cur + 56#64) gr) ∗
                A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
              Saved32x20Preserved s0 sm fsp ∧
              sm.readReg64 .x19 = cnt ∧ sm.readReg64 .x20 = cur + 56#64) := by
          dsimp only [epochDirPBHeadersAt, vecCapPtrDealloc]
          by_cases hcap : (gr.prev.cap == 0#64) = true <;>
            simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; wp_done
          · wp_steps; wp_apply; wp_steps; refine align_pre (by rw [hsp_3]; ac_rfl) ?_; wp_done
        exact SepWP.strengthen_entails_const
          (sepConj_mono_left (Entails.trans
            (sepConj_mono_right (epochDirPBHeadersAt_entails_memRegion_56 (cur + 56#64) gr))
            (chainEpochPB_regions_entails_112 cur)))
          hstep4

private theorem drop_proto_epoch_slice_placed_loop [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_288).rebase (blkPl_288).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List ChainEpochPB) (cur : BitVec 64)
      (s : State) (Frame : SepProp),
      rest ≠ [] →
      rest.length * 112 < 2 ^ 63 →
      s.pc = (blkPl_288).base + 40#64 →
      s.status = .Running →
      Saved32x20Preserved s0 s fsp →
      s.readReg64 .x19 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x20 = cur + 56#64 →
      SepWP ((blkPC_288).rebase (blkPl_288).base H)
        ((blkPl_288).base + 140#64)
        s
        (arrayAt (fun ep addr => ProtoRepr.chainEpochPBAt A addr ep) 112 cur rest ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 112) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved32x20Preserved s0 sm fsp) := by
  have hbody := drop_proto_epoch_slice_placed_body hdealloc s0 fsp hfsp_align
  intro rest
  induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons ep tl ih =>
    intro cur s Frame _ hlen hpc hrun hpres hx19 hx20
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]
    rw [sep_pull_body]
    refine seq_clean (mid := (blkPl_288).base + 28#64)
      (P_mid := memRegion cur 112 ∗ A.pool ∗ stackAt fsp allocHookStack ∗
        (arrayAt (fun ep addr => ProtoRepr.chainEpochPBAt A addr ep) 112 (cur + 112#64) tl ∗ Frame))
      (Q := fun sm => Saved32x20Preserved s0 sm fsp ∧
        sm.readReg64 .x19 = BitVec.ofNat 64 (ep :: tl).length ∧
        sm.readReg64 .x20 = cur + 56#64)
      (hbody cur (BitVec.ofNat 64 (ep :: tl).length) ep s _ hpc hrun hpres hx19 hx20)
      ?_
    intro s1 hpc1 hrun1 ⟨hpres1, hx19_1, hx20_1⟩
    rcases tl with _ | ⟨ep2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx19_1 ⊢
      rcases hpres1 with ⟨hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
      wp_steps
      wp_done
    · have hlen_tl : (ep2 :: tl2).length * 112 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_112 (n := (ep2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx19_1
      refine seq_clean (mid := (blkPl_288).base + 40#64)
        (P_mid := arrayAt (fun ep addr => ProtoRepr.chainEpochPBAt A addr ep) 112 (cur + 112#64) (ep2 :: tl2) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ (memRegion cur 112 ∗ Frame))
        (Q := fun sm => Saved32x20Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = BitVec.ofNat 64 (ep2 :: tl2).length ∧
          sm.readReg64 .x20 = (cur + 112#64) + 56#64)
        ?_ ?_
      · rcases hpres1 with ⟨hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
        rw [sep_push_body]
        wp_steps
        rw [add_112_add_56]
        wp_done
      · intro s2 hpc2 hrun2 ⟨hpres2, hx19_2, hx20_2⟩
        have hrec := ih (cur + 112#64) s2 (memRegion cur 112 ∗ Frame)
          (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hpres2 hx19_2 hx20_2
        refine SepWP.strengthen_entails_const ?_ hrec
        have hsplit := cons_len_mul ep (ep2 :: tl2) 112
        have hbound : 112 + (ep2 :: tl2).length * 112 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 112 ((ep2 :: tl2).length * 112) hbound]
        exact Entails.refl _

/-- Relocatable `core::ptr::drop_glue::<[spqr::proto::pq_ratchet::chain::Epoch]>` (Block `288`)
meets `dropProtoEpochSliceSpec A` under `[LibsignalPlacement]`. -/
theorem drop_proto_epoch_slice_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_288).rebase (blkPl_288).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_288).rebase (blkPl_288).base H)
      (blkPl_288).base (dropProtoEpochSliceSpec A) := by
  simp only [dropProtoEpochSliceSpec]
  have hloop := drop_proto_epoch_slice_placed_loop hdealloc
  dsimp only [chainEpochPBSize, BitVec.ofNat_eq_ofNat] at hloop ⊢
  wp_init x s0
  rcases x with ⟨ptr, eps⟩
  have hx0 : s0.readReg64 .x0 = ptr := h_1
  have hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 eps.length := h_2
  have hlen_lt : eps.length * 112 < 2 ^ 63 := h
  dsimp only [DropProtoEpochSliceGhost.ptr, DropProtoEpochSliceGhost.eps] at *
  cases eps with
  | nil =>
    simp only [List.length_nil, Nat.zero_mul, arrayAt, memRegion_zero, emp_sepConj] at hx1 ⊢
    wp_steps
    wp_done
  | cons ep tl =>
    have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
      spAligned_sub s0.sp 32#64 (by assumption) (by decide)
    have hne0 := ofNat_beq_zero_false_112 (n := (ep :: tl).length) (by simp) hlen_lt
    nth_rw 1 [stackAt_dropStack32_split s0.sp]
    cells_unfold
    wp_pull_exists
    wp_steps
    refine seq_clean (mid := (blkPl_288).base + 140#64)
      (P_mid := memRegion ptr ((ep :: tl).length * 112) ∗ A.pool ∗
        stackAt (s0.sp - 32#64) allocHookStack ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (Q := fun sm => Saved32x20Preserved s0 sm (s0.sp - 32#64))
      ?_ ?_
    · have hpre_eq :
          (arrayAt (fun ep addr => ProtoRepr.chainEpochPBAt A addr ep) 112 ptr (ep :: tl) ∗
            A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) =
          (arrayAt (fun ep addr => ProtoRepr.chainEpochPBAt A addr ep) 112 ptr (ep :: tl) ∗
            A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) := by
        ac_rfl
      rw [hpre_eq]
      exact hloop s0 (s0.sp - 32#64) hfsp_align (ep :: tl) ptr _ _
        (List.cons_ne_nil _ _) hlen_lt rfl (by assumption)
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        rfl rfl
    · intro sm hpcm hrunm ⟨hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
      wp_steps
      refine SepWP.weaken_pre
        (sepConj_mono_right (sepConj_mono_right (stack_restore_32_allocHook s0.sp _ _ _ _))) ?_
      wp_done

end PlacedDropGlue

/-! ## Relocatable `[LibsignalPlacement]` Join & Epilogue Lemmas (Block `364`) -/

theorem fromPb_epilogue_ret_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} (x : ChainFromPbCall) (s0 s : State)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_364).base + 1140#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
      (chainResultAt A x.out (Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗ A.pool ∗
        memRegion (s0.sp - 192#64) 96 ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  rcases htr with ⟨htr, hvregs⟩
  unfold calleeSavedFromPbAt
  wp_steps
  refine SepWP.focus_weaken (restore_stack_192_chainFromPb s0) (by
    unfold calleeSavedFromPbAt; sep_focus) ?_
  wp_done

theorem fromPb_epilogue_dealloc_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (x : ChainFromPbCall) (s0 s : State) (nrCap nrPtr : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hnr_ne : nrCap ≠ 0) (_hnr_lt : nrCap.toNat < 2 ^ 63) (_hnr_ptr : nrPtr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 1008#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 .x0 = nrPtr) (hx1 : s.readReg64 .x1 = nrCap) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
      (chainResultAt A x.out (Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗ A.pool ∗
        A.live nrPtr nrCap.toNat 1 ∗ memRegion nrPtr nrCap.toNat ∗
        memRegion (s0.sp - 192#64) 96 ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  have hnr_pos : nrCap.toNat > 0 := Nat.pos_of_ne_zero (by
    intro h0; exact hnr_ne (BitVec.eq_of_toNat_eq (by simpa using h0)))
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  rcases htr with ⟨htr, hvregs⟩
  unfold calleeSavedFromPbAt
  wp_steps
  refine SepWP.focus_weaken (restore_stack_192_chainFromPb s0) (by
    unfold calleeSavedFromPbAt; sep_focus) ?_
  rw [stackAt_chainFromPb_split_allocHook s0.sp]
  wp_call hdealloc (nrPtr, nrCap.toNat, 1)
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_chainFromPb_split_allocHook s0.sp).symm)
    (by sep_focus) ?_
  wp_done

set_option maxHeartbeats 800000 in
theorem fromPb_bad_direction_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hproto_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 288) (dropProtoEpochSliceSpec A))
    (x : ChainFromPbCall) (s0 s : State)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hdir_uge : BitVec.ule 2#32 x.pb.direction = true)
    (hlen : x.gPb.epochs.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (_hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 292#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hx24 : s.readReg64 .x24 = x.out) (hx25 : s.readReg64 .x25 = x.pbPtr) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochPBAt A) 112 x.gPb.linksPtr (x.gPb.epochs.zip x.pb.links) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        memRegion (s0.sp - 192#64) 96 ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  have hep_ret := @fromPb_epilogue_ret_placed _ A H x s0
  have hep_dealloc := @fromPb_epilogue_dealloc_placed _ A H hdealloc x s0
  have hlen_lt : x.pb.links.length * 112 < 2 ^ 63 :=
    lt_of_le_of_lt (Nat.mul_le_mul_right 112 hl_le) hl_lt
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  have hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode :=
    chainFromPb_of_direction_uge_two hdir_uge
  refine SepWP.focus_weaken
    (arrayAt_chainEpochPBAt_entails_protoRepr A x.gPb.epochs x.pb.links x.gPb.linksPtr hlen)
    (by sep_focus) ?_
  refine SepWP.focus_weaken
    (vecU8BufAt_entails_dealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot hn_le hn_lt)
    (by sep_focus) ?_
  rw [memRegion_88_words4_rest x.out]
  wp_pull_exists
  dsimp only [dropProtoEpochSliceSpec,
    ProtoRepr.chainEpochPBSize, BitVec.ofNat_eq_ofNat] at hep_ret hep_dealloc hproto_slice hdealloc hpc ⊢
  refine seq_clean (mid := (blkPl_364).base + 316#64)
    (P_mid := chainResultAt A x.out (Chain.fromPb x.pb) ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
      memRegion x.gPb.linksPtr (x.pb.links.length * 112) ∗
      linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecCapPtrDealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗ A.pool ∗
      memRegion (s0.sp - 192#64) 96 ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .x19 = x.gPb.linksPtr ∧ sm.readReg64 .x25 = x.pbPtr) ?_ ?_
  · unfold chainPBHeadersAt
    rw [stackAt_subStack_split_dropStack32 s0.sp]
    wp_steps
    refine SepWP.focus_weaken
      (err_stateDecode_pack_words A x.out x.pb hfromPb_eq _ _ _ (bitvec_low_byte_clear_zero _))
      (by sep_focus) ?_
    wp_call hproto_slice ⟨x.gPb.linksPtr, x.pb.links⟩
    rw [hsp]; wp_done
  · rintro s1 hpc1 hrun1 ⟨hsp1, htr1, hx19_1, hx25_1⟩
    refine SepWP.focus_weaken
      (linksRawAllocAt_combine_memRegion A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length hl_le hl_lt)
      (by sep_focus) ?_
    refine seq_clean (mid := (blkPl_364).base + 344#64)
      (P_mid := chainResultAt A x.out (Chain.fromPb x.pb) ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        vecCapPtrDealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗ A.pool ∗
        memRegion (s0.sp - 192#64) 96 ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
        sm.readReg64 .x25 = x.pbPtr) ?_ ?_
    · unfold chainPBHeadersAt
      by_cases hc : x.gPb.linksCap = 0
      · have hcb : (x.gPb.linksCap == 0#64) = true := beq_iff_eq.mpr hc
        simp only [hcb, ↓reduceIte, emp_sepConj, sepConj_emp]; wp_steps; wp_done
      · have hcb : (x.gPb.linksCap == 0#64) = false := beq_eq_false_iff_ne.mpr hc
        have hpos : x.gPb.linksCap.toNat * 112 > 0 := by
          have : x.gPb.linksCap.toNat > 0 := Nat.pos_of_ne_zero (by
            intro hz; exact hc (BitVec.eq_of_toNat_eq (by simpa using hz)))
          omega
        have hlsl := cap_mul_112_shift_eq x.gPb.linksCap hl_lt
        simp only [hcb, Bool.false_eq_true, ↓reduceIte]
        rw [stackAt_subStack_split_allocHook s0.sp]
        wp_steps
        wp_call hdealloc (x.gPb.linksPtr, x.gPb.linksCap.toNat * 112, 8)
        rw [hsp1]; wp_done
    · rintro s2 hpc2 hrun2 ⟨hsp2, htr2, hx25_2⟩
      by_cases hnr : x.gPb.nextRoot.cap = 0
      · have hnrb : (x.gPb.nextRoot.cap == 0#64) = true := beq_iff_eq.mpr hnr
        unfold vecCapPtrDealloc
        simp only [hnrb, ↓reduceIte, emp_sepConj, sepConj_emp]
        refine seq_clean (mid := (blkPl_364).base + 1140#64)
          (P_mid := chainResultAt A x.out (Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗ A.pool ∗
            memRegion (s0.sp - 192#64) 96 ∗ calleeSavedFromPbAt s0 ∗
            stackAt (s0.sp - 192#64) chainFromPbSubStack)
          (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0) ?_ ?_
        · unfold chainPBHeadersAt; wp_steps
          refine SepWP.focus_weaken
            (chainPBHeadersAt_entails_memRegion_80 x.pbPtr x.gPb x.pb)
            (by unfold chainPBHeadersAt; sep_focus) ?_
          wp_done
        · rintro s3 hpc3 hrun3 ⟨hsp3, htr3⟩
          exact hep_ret s3 hsp0_align hpc3 hrun3 hsp3 htr3
      · have hnrb : (x.gPb.nextRoot.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hnr
        unfold vecCapPtrDealloc
        simp only [hnrb, Bool.false_eq_true, ↓reduceIte]
        refine seq_clean (mid := (blkPl_364).base + 1008#64)
          (P_mid := chainResultAt A x.out (Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗ A.pool ∗
            A.live x.gPb.nextRoot.ptr x.gPb.nextRoot.cap.toNat 1 ∗
            memRegion x.gPb.nextRoot.ptr x.gPb.nextRoot.cap.toNat ∗
            memRegion (s0.sp - 192#64) 96 ∗ calleeSavedFromPbAt s0 ∗
            stackAt (s0.sp - 192#64) chainFromPbSubStack)
          (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
            sm.readReg64 .x0 = x.gPb.nextRoot.ptr ∧ sm.readReg64 .x1 = x.gPb.nextRoot.cap) ?_ ?_
        · unfold chainPBHeadersAt; wp_steps
          refine SepWP.focus_weaken
            (chainPBHeadersAt_entails_memRegion_80 x.pbPtr x.gPb x.pb)
            (by unfold chainPBHeadersAt; sep_focus) ?_
          wp_done
        · rintro s3 hpc3 hrun3 ⟨hsp3, htr3, hx0_3, hx1_3⟩
          exact hep_dealloc s3 x.gPb.nextRoot.cap x.gPb.nextRoot.ptr
            hsp0_align hnr hn_lt hn_ne hpc3 hrun3 hsp3 htr3 hx0_3 hx1_3

set_option maxHeartbeats 800000 in
theorem fromPb_join_err_tail_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hchain_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 287) (dropChainEpochSliceSpec A))
    (x : ChainFromPbCall) (s0 s : State)
    (convEpochs : List ChainEpoch) (remPB : List ChainEpochPB) (sp0_val : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode)
    (hsplit_len : convEpochs.length + 1 + remPB.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 944#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hx19 : s.readReg64 .x19 = 0#64) (hx21 : s.readReg64 .x21 = x.gPb.nextRoot.cap)
    (hx22 : s.readReg64 .x22 = x.gPb.nextRoot.ptr) (hx24 : s.readReg64 .x24 = x.out)
    (hx25 : s.readReg64 .x25 = x.gPb.linksCap) (hx26 : s.readReg64 .x26 = x.gPb.linksPtr)
    (hx27 : s.readReg64 .x27 = 0#64) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ memRegion x.pbPtr 80 ∗
        memRegion x.gPb.linksPtr (convEpochs.length * 112) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remPB.length * 112) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecCapPtrDealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗ A.pool ∗
        joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  have hep_ret := @fromPb_epilogue_ret_placed _ A H x s0
  have hep_dealloc := @fromPb_epilogue_dealloc_placed _ A H hdealloc x s0
  have hlen_lt : x.pb.links.length * 112 < 2 ^ 63 :=
    lt_of_le_of_lt (Nat.mul_le_mul_right 112 hl_le) hl_lt
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  dsimp only [dropChainEpochSliceSpec,
    chainEpochSize, BitVec.ofNat_eq_ofNat] at hep_ret hep_dealloc hchain_slice hdealloc hpc ⊢
  refine seq_clean (mid := (blkPl_364).base + 956#64)
    (P_mid := memRegion x.out 88 ∗ memRegion x.pbPtr 80 ∗
      memRegion x.gPb.linksPtr (convEpochs.length * 112) ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remPB.length * 112) ∗
      linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecCapPtrDealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗ A.pool ∗
      joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
      sm.readReg64 .x24 = x.out ∧ sm.readReg64 .x25 = x.gPb.linksCap ∧
      sm.readReg64 .x26 = x.gPb.linksPtr ∧ sm.readReg64 .x27 = 0#64) ?_ ?_
  · refine SepWP.focus_weaken
      (pool_entails_empty_arrayAt_pool A (chainEpoch A) 112 x.gPb.linksPtr) (by sep_focus) ?_
    rw [stackAt_subStack_split_dropStack32 s0.sp]
    wp_steps
    wp_call hchain_slice ⟨x.gPb.linksPtr, []⟩
    rw [hsp, memRegion_zero, emp_sepConj]; wp_done
  · rintro s3 hpc3 hrun3 ⟨hsp3, htr3, hx21_3, hx22_3, hx24_3, hx25_3, hx26_3, hx27_3⟩
    have hjoin3 :
        memRegion x.gPb.linksPtr (convEpochs.length * 112) ∗
          memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
          memRegion (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remPB.length * 112) ⊢
          memRegion x.gPb.linksPtr (x.pb.links.length * 112) := by
      rw [← hsplit_len]
      exact memRegion_join_three_112 x.gPb.linksPtr convEpochs.length remPB.length
        (by rw [hsplit_len]; exact hlen_lt)
    refine SepWP.focus_weaken hjoin3 (by sep_focus) ?_
    refine SepWP.focus_weaken
      (linksRawAllocAt_combine_memRegion A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length hl_le hl_lt)
      (by sep_focus) ?_
    refine seq_clean (mid := (blkPl_364).base + 980#64)
      (P_mid := memRegion x.out 88 ∗ memRegion x.pbPtr 80 ∗
        vecCapPtrDealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗ A.pool ∗
        joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
        sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
        sm.readReg64 .x24 = x.out ∧ sm.readReg64 .x27 = 0#64) ?_ ?_
    · by_cases hc : x.gPb.linksCap = 0
      · have hcb : (x.gPb.linksCap == 0#64) = true := beq_iff_eq.mpr hc
        simp only [hcb, ↓reduceIte, emp_sepConj, sepConj_emp]; wp_steps; wp_done
      · have hcb : (x.gPb.linksCap == 0#64) = false := beq_eq_false_iff_ne.mpr hc
        have hpos : x.gPb.linksCap.toNat * 112 > 0 := by
          have : x.gPb.linksCap.toNat > 0 := Nat.pos_of_ne_zero (by
            intro hz; exact hc (BitVec.eq_of_toNat_eq (by simpa using hz)))
          omega
        have hlsl := cap_mul_112_shift_eq x.gPb.linksCap hl_lt
        simp only [hcb, Bool.false_eq_true, ↓reduceIte]
        rw [stackAt_subStack_split_allocHook s0.sp]
        wp_steps
        wp_call hdealloc (x.gPb.linksPtr, x.gPb.linksCap.toNat * 112, 8)
        rw [hsp3]; wp_done
    · rintro s4 hpc4 hrun4 ⟨hsp4, htr4, hx21_4, hx22_4, hx24_4, hx27_4⟩
      rw [memRegion_88_words4_rest x.out]
      wp_pull_exists
      unfold vecCapPtrDealloc
      by_cases hnr : x.gPb.nextRoot.cap = 0
      · have hnrb : (x.gPb.nextRoot.cap == 0#64) = true := beq_iff_eq.mpr hnr
        simp only [hnrb, ↓reduceIte, emp_sepConj, sepConj_emp]
        refine seq_clean (mid := (blkPl_364).base + 1140#64)
          (P_mid := chainResultAt A x.out (Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗ A.pool ∗
            memRegion (s0.sp - 192#64) 96 ∗ calleeSavedFromPbAt s0 ∗
            stackAt (s0.sp - 192#64) chainFromPbSubStack)
          (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0) ?_ ?_
        · unfold joinScratchAt; wp_steps
          refine SepWP.focus_weaken
            (err_stateDecode_pack_words A x.out x.pb hfromPb_eq 0#64 sp0_val _ rfl)
            (by sep_focus) ?_
          refine SepWP.focus_weaken
            (joinScratchAt_entails_memRegion_96 s0 x.gPb x.pb sp0_val)
            (by unfold joinScratchAt; sep_focus) ?_
          wp_done
        · rintro s5 hpc5 hrun5 ⟨hsp5, htr5⟩
          exact hep_ret s5 hsp0_align hpc5 hrun5 hsp5 htr5
      · have hnrb : (x.gPb.nextRoot.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hnr
        simp only [hnrb, Bool.false_eq_true, ↓reduceIte]
        refine seq_clean (mid := (blkPl_364).base + 1008#64)
          (P_mid := chainResultAt A x.out (Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗ A.pool ∗
            A.live x.gPb.nextRoot.ptr x.gPb.nextRoot.cap.toNat 1 ∗
            memRegion x.gPb.nextRoot.ptr x.gPb.nextRoot.cap.toNat ∗
            memRegion (s0.sp - 192#64) 96 ∗ calleeSavedFromPbAt s0 ∗
            stackAt (s0.sp - 192#64) chainFromPbSubStack)
          (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
            sm.readReg64 .x0 = x.gPb.nextRoot.ptr ∧ sm.readReg64 .x1 = x.gPb.nextRoot.cap) ?_ ?_
        · unfold joinScratchAt; wp_steps
          refine SepWP.focus_weaken
            (err_stateDecode_pack_words A x.out x.pb hfromPb_eq 0#64 sp0_val _ rfl)
            (by sep_focus) ?_
          refine SepWP.focus_weaken
            (joinScratchAt_entails_memRegion_96 s0 x.gPb x.pb sp0_val)
            (by unfold joinScratchAt; sep_focus) ?_
          wp_done
        · rintro s5 hpc5 hrun5 ⟨hsp5, htr5, hx0_5, hx1_5⟩
          exact hep_dealloc s5 x.gPb.nextRoot.cap x.gPb.nextRoot.ptr
            hsp0_align hnr hn_lt hn_ne hpc5 hrun5 hsp5 htr5 hx0_5 hx1_5

set_option maxHeartbeats 800000 in
theorem fromPb_join_err_840_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hchain_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 287) (dropChainEpochSliceSpec A))
    (x : ChainFromPbCall) (s0 s : State)
    (convEpochs : List ChainEpoch) (remPB : List ChainEpochPB) (sp0_val : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode)
    (hsplit_len : convEpochs.length + 1 + remPB.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 840#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64) (hx19 : s.readReg64 .x19 = 0#64)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 convEpochs.length)
    (hx21 : s.readReg64 .x21 = x.gPb.nextRoot.cap) (hx22 : s.readReg64 .x22 = x.gPb.nextRoot.ptr)
    (hx23 : s.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (hx24 : s.readReg64 .x24 = x.out) (hx26 : s.readReg64 .x26 = x.gPb.linksPtr)
    (hx27 : s.readReg64 .x27 = 0#64) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ memRegion x.pbPtr 80 ∗
        arrayAt (chainEpoch A) 112 x.gPb.linksPtr convEpochs ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remPB.length * 112) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecCapPtrDealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗ A.pool ∗
        joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  have htail := @fromPb_join_err_tail_placed _ A H hdealloc hchain_slice x s0
  have hlen_lt : x.pb.links.length * 112 < 2 ^ 63 :=
    lt_of_le_of_lt (Nat.mul_le_mul_right 112 hl_le) hl_lt
  have hconv_lt : convEpochs.length * 112 < 2 ^ 63 := by
    have : convEpochs.length ≤ x.pb.links.length := by omega
    exact lt_of_le_of_lt (Nat.mul_le_mul_right 112 this) hlen_lt
  have hconv_le_cap : convEpochs.length ≤ x.gPb.linksCap.toNat := by omega
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  have hcsel1 := csel_sub_zero_of_le convEpochs.length x.gPb.linksCap hconv_le_cap
  have hcsel1_ult := csel_ult_sub_zero_of_le convEpochs.length x.gPb.linksCap hconv_le_cap
  have hcsel2 := csel_min_eq_of_le convEpochs.length x.gPb.linksCap hconv_le_cap
  have hcsel2_ult := csel_ult_min_eq_of_le convEpochs.length x.gPb.linksCap hconv_le_cap
  have hcsel3 := csel_zero_if_ptr_eq x.gPb.linksPtr convEpochs.length hconv_lt
  have hcsel3_eq := csel_eq_zero_if_ptr_eq x.gPb.linksPtr convEpochs.length hconv_lt
  dsimp only [dropChainEpochSliceSpec,
    chainEpochSize, BitVec.ofNat_eq_ofNat] at htail hchain_slice hpc ⊢
  refine seq_clean (mid := (blkPl_364).base + 944#64)
    (P_mid := memRegion x.out 88 ∗ memRegion x.pbPtr 80 ∗
      memRegion x.gPb.linksPtr (convEpochs.length * 112) ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remPB.length * 112) ∗
      linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecCapPtrDealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗ A.pool ∗
      joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .x19 = 0#64 ∧ sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧
      sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧ sm.readReg64 .x24 = x.out ∧
      sm.readReg64 .x25 = x.gPb.linksCap ∧ sm.readReg64 .x26 = x.gPb.linksPtr ∧
      sm.readReg64 .x27 = 0#64) ?_ ?_
  · unfold joinScratchAt
    rw [stackAt_subStack_split_dropStack32 s0.sp]
    wp_steps
    wp_call hchain_slice ⟨x.gPb.linksPtr, convEpochs⟩
    rw [hsp]; wp_done
  · rintro s2 hpc2 hrun2 ⟨hsp2, htr2, hx19_2, hx21_2, hx22_2, hx24_2, hx25_2, hx26_2, hx27_2⟩
    exact htail s2 convEpochs remPB sp0_val hsp0_align hfromPb_eq hsplit_len hl_le hl_lt hn_lt hn_ne
      hpc2 hrun2 hsp2 htr2 hx19_2 hx21_2 hx22_2 hx24_2 hx25_2 hx26_2 hx27_2

set_option maxHeartbeats 800000 in
theorem fromPb_join_err_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hchain_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 287) (dropChainEpochSliceSpec A))
    (hproto_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 288) (dropProtoEpochSliceSpec A))
    (x : ChainFromPbCall) (s0 s : State)
    (convG : List ChainEpochGhost) (convEpochs : List ChainEpoch)
    (remG : List ChainEpochPBGhost) (remPB : List ChainEpochPB) (sp0_val : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode)
    (hconv_len : convG.length = convEpochs.length) (hrem_len : remG.length = remPB.length)
    (hsplit_len : convEpochs.length + 1 + remPB.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (_hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 792#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hx29 : s.readReg64 .fp = s0.sp - 96#64)
    (hx0 : s.readReg64 .x0 = x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112))
    (hx11 : s.readReg64 .x11 = x.gPb.linksPtr) (hx19 : s.readReg64 .x19 = 0#64)
    (hx20 : s.readReg64 .x20 = x.gPb.linksPtr + BitVec.ofNat 64 (x.pb.links.length * 112))
    (hx21 : s.readReg64 .x21 = x.gPb.nextRoot.cap) (hx22 : s.readReg64 .x22 = x.gPb.nextRoot.ptr)
    (hx23 : s.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (hx24 : s.readReg64 .x24 = x.out) (hx27 : s.readReg64 .x27 = 0#64) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        arrayAt (chainEpochPBAt A) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  have h840 := @fromPb_join_err_840_placed _ A H hdealloc hchain_slice x s0
  have hlen_lt : x.pb.links.length * 112 < 2 ^ 63 :=
    lt_of_le_of_lt (Nat.mul_le_mul_right 112 hl_le) hl_lt
  have hrem_lt : remPB.length * 112 < 2 ^ 63 := by
    have : remPB.length ≤ x.pb.links.length := by omega
    exact lt_of_le_of_lt (Nat.mul_le_mul_right 112 this) hlen_lt
  have hconv_lt : convEpochs.length * 112 < 2 ^ 63 := by
    have : convEpochs.length ≤ x.pb.links.length := by omega
    exact lt_of_le_of_lt (Nat.mul_le_mul_right 112 this) hlen_lt
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  have hsub_rem := sub_links_rem_112 x.gPb.linksPtr convEpochs.length remPB.length
    x.pb.links.length hsplit_len
  have hsub_conv := sub_links_conv_112 x.gPb.linksPtr convEpochs.length
  have hdiv_rem := div_112_magic_eq hrem_lt
  have hdiv_rem_nat := div_112_magic_nat_eq hrem_lt
  have hdiv_conv := div_112_magic_eq hconv_lt
  have hdiv_conv_nat := div_112_magic_nat_eq hconv_lt
  refine SepWP.focus_weaken
    (arrayAt_chainEpochPBAt_entails_protoRepr A remG remPB
      (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) hrem_len)
    (by sep_focus) ?_
  refine SepWP.focus_weaken
    (arrayAt_chainEpochAt_entails_unpinned A convG convEpochs x.gPb.linksPtr hconv_len)
    (by sep_focus) ?_
  refine SepWP.focus_weaken
    (vecU8BufAt_entails_dealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot hn_le hn_lt)
    (by sep_focus) ?_
  refine SepWP.focus_weaken
    (chainPBHeadersAt_entails_memRegion_80 x.pbPtr x.gPb x.pb) (by sep_focus) ?_
  dsimp only [dropProtoEpochSliceSpec,
    ProtoRepr.chainEpochPBSize, BitVec.ofNat_eq_ofNat] at h840 hproto_slice hpc ⊢
  refine seq_clean (mid := (blkPl_364).base + 840#64)
    (P_mid := memRegion x.out 88 ∗ memRegion x.pbPtr 80 ∗
      arrayAt (chainEpoch A) 112 x.gPb.linksPtr convEpochs ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remPB.length * 112) ∗
      linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecCapPtrDealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗ A.pool ∗
      joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x19 = 0#64 ∧
      sm.readReg64 .x20 = BitVec.ofNat 64 convEpochs.length ∧
      sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
      sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
      sm.readReg64 .x24 = x.out ∧ sm.readReg64 .x26 = x.gPb.linksPtr ∧
      sm.readReg64 .x27 = 0#64) ?_ ?_
  · rw [stackAt_subStack_split_dropStack32 s0.sp]
    wp_steps
    wp_call hproto_slice ⟨x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112), remPB⟩
    rw [hsp]; wp_done
  · rintro s1 hpc1 hrun1 ⟨hsp1, htr1, hfp1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx26_1, hx27_1⟩
    exact h840 s1 convEpochs remPB sp0_val hsp0_align hfromPb_eq hsplit_len hl_le hl_lt hn_lt hn_ne
      hpc1 hrun1 hsp1 htr1 hfp1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx26_1 hx27_1

set_option maxHeartbeats 800000 in
theorem fromPb_join_params_none_tail_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hchain_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 287) (dropChainEpochSliceSpec A))
    (x : ChainFromPbCall) (s0 s : State)
    (convEpochs : List ChainEpoch) (sp0_val : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpb_len : convEpochs.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 1100#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hx19 : s.readReg64 .x19 = 0#64) (hx20 : s.readReg64 .x20 = x.gPb.linksPtr)
    (hx21 : s.readReg64 .x21 = x.gPb.nextRoot.cap) (hx22 : s.readReg64 .x22 = x.gPb.nextRoot.ptr)
    (hx25 : s.readReg64 .x25 = x.gPb.linksCap) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
      (chainResultAt A x.out (Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗
        memRegion x.gPb.linksPtr (convEpochs.length * 112) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecCapPtrDealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗ A.pool ∗
        joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  have hep_ret := @fromPb_epilogue_ret_placed _ A H x s0
  have hep_dealloc := @fromPb_epilogue_dealloc_placed _ A H hdealloc x s0
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  dsimp only [dropChainEpochSliceSpec,
    chainEpochSize, BitVec.ofNat_eq_ofNat] at hep_ret hep_dealloc hchain_slice hdealloc hpc ⊢
  refine seq_clean (mid := (blkPl_364).base + 1112#64)
    (P_mid := chainResultAt A x.out (Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗
      memRegion x.gPb.linksPtr (convEpochs.length * 112) ∗
      linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecCapPtrDealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗ A.pool ∗
      joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .x20 = x.gPb.linksPtr ∧ sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧
      sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧ sm.readReg64 .x25 = x.gPb.linksCap) ?_ ?_
  · refine SepWP.focus_weaken
      (pool_entails_empty_arrayAt_pool A (chainEpoch A) 112 x.gPb.linksPtr) (by sep_focus) ?_
    rw [stackAt_subStack_split_dropStack32 s0.sp]
    wp_steps
    wp_call hchain_slice ⟨x.gPb.linksPtr, []⟩
    rw [hsp, memRegion_zero, emp_sepConj]; wp_done
  · rintro s3 hpc3 hrun3 ⟨hsp3, htr3, hx20_3, hx21_3, hx22_3, hx25_3⟩
    rw [hpb_len]
    refine SepWP.focus_weaken
      (linksRawAllocAt_combine_memRegion A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length hl_le hl_lt)
      (by sep_focus) ?_
    refine seq_clean (mid := (blkPl_364).base + 1136#64)
      (P_mid := chainResultAt A x.out (Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗
        vecCapPtrDealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗ A.pool ∗
        joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
        sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr) ?_ ?_
    · by_cases hc : x.gPb.linksCap = 0
      · have hcb : (x.gPb.linksCap == 0#64) = true := beq_iff_eq.mpr hc
        simp only [hcb, ↓reduceIte, emp_sepConj, sepConj_emp]; wp_steps; wp_done
      · have hcb : (x.gPb.linksCap == 0#64) = false := beq_eq_false_iff_ne.mpr hc
        have hpos : x.gPb.linksCap.toNat * 112 > 0 := by
          have : x.gPb.linksCap.toNat > 0 := Nat.pos_of_ne_zero (by
            intro hz; exact hc (BitVec.eq_of_toNat_eq (by simpa using hz)))
          omega
        have hlsl := cap_mul_112_shift_eq x.gPb.linksCap hl_lt
        simp only [hcb, Bool.false_eq_true, ↓reduceIte]
        rw [stackAt_subStack_split_allocHook s0.sp]
        wp_steps
        wp_call hdealloc (x.gPb.linksPtr, x.gPb.linksCap.toNat * 112, 8)
        rw [hsp3]; wp_done
    · rintro s4 hpc4 hrun4 ⟨hsp4, htr4, hx21_4, hx22_4⟩
      unfold vecCapPtrDealloc
      refine SepWP.focus_weaken
        (joinScratchAt_entails_memRegion_96 s0 x.gPb x.pb sp0_val) (by sep_focus) ?_
      by_cases hnr : x.gPb.nextRoot.cap = 0
      · have hnrb : (x.gPb.nextRoot.cap == 0#64) = true := beq_iff_eq.mpr hnr
        simp only [hnrb, ↓reduceIte, emp_sepConj, sepConj_emp]
        refine seq_clean (mid := (blkPl_364).base + 1140#64)
          (P_mid := chainResultAt A x.out (Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗ A.pool ∗
            memRegion (s0.sp - 192#64) 96 ∗ calleeSavedFromPbAt s0 ∗
            stackAt (s0.sp - 192#64) chainFromPbSubStack)
          (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0) ?_ ?_
        · wp_steps; wp_done
        · rintro s5 hpc5 hrun5 ⟨hsp5, htr5⟩
          exact hep_ret s5 hsp0_align hpc5 hrun5 hsp5 htr5
      · have hnrb : (x.gPb.nextRoot.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hnr
        simp only [hnrb, Bool.false_eq_true, ↓reduceIte]
        refine seq_clean (mid := (blkPl_364).base + 1008#64)
          (P_mid := chainResultAt A x.out (Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗ A.pool ∗
            A.live x.gPb.nextRoot.ptr x.gPb.nextRoot.cap.toNat 1 ∗
            memRegion x.gPb.nextRoot.ptr x.gPb.nextRoot.cap.toNat ∗
            memRegion (s0.sp - 192#64) 96 ∗ calleeSavedFromPbAt s0 ∗
            stackAt (s0.sp - 192#64) chainFromPbSubStack)
          (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
            sm.readReg64 .x0 = x.gPb.nextRoot.ptr ∧ sm.readReg64 .x1 = x.gPb.nextRoot.cap) ?_ ?_
        · wp_steps; wp_done
        · rintro s5 hpc5 hrun5 ⟨hsp5, htr5, hx0_5, hx1_5⟩
          exact hep_dealloc s5 x.gPb.nextRoot.cap x.gPb.nextRoot.ptr
            hsp0_align hnr hn_lt hn_ne hpc5 hrun5 hsp5 htr5 hx0_5 hx1_5

set_option maxHeartbeats 800000 in
theorem fromPb_join_ok_840_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hchain_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 287) (dropChainEpochSliceSpec A))
    (x : ChainFromPbCall) (s0 s : State) (dir : Direction)
    (convG : List ChainEpochGhost) (convEpochs : List ChainEpoch) (sp0_val : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hdir : Direction.fromI32? x.pb.direction = some dir) (hdir_i32 : dir.toI32 = x.pb.direction)
    (hlinks : Chain.linksFromPb x.pb.links = .ok convEpochs)
    (hconv_len : convG.length = convEpochs.length) (hpb_len : convEpochs.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 840#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64) (hx19 : s.readReg64 .x19 = 1#64)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 convEpochs.length)
    (hx21 : s.readReg64 .x21 = x.gPb.nextRoot.cap) (hx22 : s.readReg64 .x22 = x.gPb.nextRoot.ptr)
    (hx23 : s.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (hx24 : s.readReg64 .x24 = x.out) (hx25 : s.readReg64 .x25 = x.pbPtr) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  have hep_ret := @fromPb_epilogue_ret_placed _ A H x s0
  have hnone_tail := @fromPb_join_params_none_tail_placed _ A H hdealloc hchain_slice x s0
  have hlen_lt : x.pb.links.length * 112 < 2 ^ 63 :=
    lt_of_le_of_lt (Nat.mul_le_mul_right 112 hl_le) hl_lt
  have hconv_lt : convEpochs.length * 112 < 2 ^ 63 := by rw [hpb_len]; exact hlen_lt
  have hconv_le_cap : convEpochs.length ≤ x.gPb.linksCap.toNat := by rw [hpb_len]; exact hl_le
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  dsimp only [dropChainEpochSliceSpec,
    chainEpochSize, BitVec.ofNat_eq_ofNat] at hep_ret hnone_tail hchain_slice hpc ⊢
  cases hp : x.pb.params with
  | some cp =>
    have hfromPb_eq : Chain.fromPb x.pb = .ok {
        dir := dir, currentEpoch := x.pb.currentEpoch, sendEpoch := x.pb.sendEpoch,
        nextRoot := x.pb.nextRoot, links := convEpochs, params := cp } :=
      chainFromPb_of_ok hdir hlinks hp
    rw [memRegion_88_words4_rest x.out, memRegion_56_split_chainTail x.out]
    wp_pull_exists
    refine seq_clean (mid := (blkPl_364).base + 1140#64)
      (P_mid := chainResultAt A x.out (Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗ A.pool ∗
        memRegion (s0.sp - 192#64) 96 ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0) ?_ ?_
    · unfold chainPBHeadersAt optChainParamsPBAt joinScratchAt
      rw [hp]; dsimp only
      wp_steps
      have hhdr :
          (x.pbPtr ↦₆₄ x.gPb.linksCap) ∗ ((x.pbPtr + 8#64) ↦₆₄ x.gPb.linksPtr) ∗
            ((x.pbPtr + 16#64) ↦₆₄ BitVec.ofNat 64 x.pb.links.length) ∗
            ((x.pbPtr + 24#64) ↦₆₄ x.gPb.nextRoot.cap) ∗ ((x.pbPtr + 32#64) ↦₆₄ x.gPb.nextRoot.ptr) ∗
            ((x.pbPtr + 40#64) ↦₆₄ BitVec.ofNat 64 x.pb.nextRoot.length) ∗
            ((x.pbPtr + 48#64) ↦₆₄ x.pb.currentEpoch) ∗ ((x.pbPtr + 56#64) ↦₆₄ x.pb.sendEpoch) ∗
            (((x.pbPtr + 64#64) ↦₃₂ 1#32) ∗ ((x.pbPtr + 64#64 + 4#64) ↦₃₂ cp.maxJump) ∗
              ((x.pbPtr + 64#64 + 8#64) ↦₃₂ cp.maxOooKeys)) ∗
            ((x.pbPtr + 76#64) ↦₃₂ x.pb.direction) ⊢ memRegion x.pbPtr 80 := by
        have := chainPBHeadersAt_entails_memRegion_80 x.pbPtr x.gPb x.pb
        unfold chainPBHeadersAt optChainParamsPBAt at this; rw [hp] at this; exact this
      refine SepWP.focus_weaken hhdr (by sep_focus) ?_
      have hpack :
          (x.out ↦₆₄ x.gPb.linksCap) ∗ ((x.out + 8#64) ↦₆₄ x.gPb.linksPtr) ∗
            ((x.out + 16#64) ↦₆₄ 0#64) ∗ ((x.out + 24#64) ↦₆₄ BitVec.ofNat 64 x.pb.links.length) ∗
            ((x.out + 32#64) ↦₆₄ x.gPb.nextRoot.cap) ∗ ((x.out + 40#64) ↦₆₄ x.gPb.nextRoot.ptr) ∗
            ((x.out + 48#64) ↦₆₄ BitVec.ofNat 64 x.pb.nextRoot.length) ∗
            ((x.out + 56#64) ↦₆₄ x.pb.currentEpoch) ∗ ((x.out + 64#64) ↦₆₄ x.pb.sendEpoch) ∗
            ((x.out + 72#64) ↦₃₂ cp.maxJump) ∗ ((x.out + 76#64) ↦₃₂ cp.maxOooKeys) ∗
            ((x.out + 80#64) ↦₃₂ x.pb.direction) ∗ memRegion (x.out + 84#64) 4 ∗
            arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
            linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
            vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ⊢
            chainResultAt A x.out (Chain.fromPb x.pb) := by
        rw [hfromPb_eq, ← hdir_i32, ← hpb_len]
        exact chainResultAt_ok_pack A x.out x.gPb.linksCap x.gPb.linksPtr
          x.gPb.nextRoot.cap x.gPb.nextRoot.ptr convG convEpochs x.pb.nextRoot
          x.pb.currentEpoch x.pb.sendEpoch cp dir
          hconv_len hconv_le_cap hl_lt hl_ne hn_le hn_lt hn_ne
      refine SepWP.focus_weaken hpack (by sep_focus) ?_
      refine SepWP.focus_weaken
        (joinScratchAt_entails_memRegion_96 s0 x.gPb x.pb sp0_val)
        (by unfold joinScratchAt; sep_focus) ?_
      wp_done
    · rintro s2 hpc2 hrun2 ⟨hsp2, htr2⟩
      exact hep_ret s2 hsp0_align hpc2 hrun2 hsp2 htr2
  | none =>
    have hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode :=
      chainFromPb_of_params_none hdir hlinks hp
    have hcsel1 := csel_sub_zero_of_le convEpochs.length x.gPb.linksCap hconv_le_cap
    have hcsel1_ult := csel_ult_sub_zero_of_le convEpochs.length x.gPb.linksCap hconv_le_cap
    have hcsel2 := csel_min_eq_of_le convEpochs.length x.gPb.linksCap hconv_le_cap
    have hcsel2_ult := csel_ult_min_eq_of_le convEpochs.length x.gPb.linksCap hconv_le_cap
    have hcsel3 := csel_zero_if_ptr_eq x.gPb.linksPtr convEpochs.length hconv_lt
    have hcsel3_eq := csel_eq_zero_if_ptr_eq x.gPb.linksPtr convEpochs.length hconv_lt
    have hcsel1_pb := csel_sub_zero_of_le x.pb.links.length x.gPb.linksCap hl_le
    have hcsel1_ult_pb := csel_ult_sub_zero_of_le x.pb.links.length x.gPb.linksCap hl_le
    have hcsel2_pb := csel_min_eq_of_le x.pb.links.length x.gPb.linksCap hl_le
    have hcsel2_ult_pb := csel_ult_min_eq_of_le x.pb.links.length x.gPb.linksCap hl_le
    have hcsel3_pb := csel_zero_if_ptr_eq x.gPb.linksPtr x.pb.links.length hlen_lt
    have hcsel3_eq_pb := csel_eq_zero_if_ptr_eq x.gPb.linksPtr x.pb.links.length hlen_lt
    refine SepWP.focus_weaken
      (arrayAt_chainEpochAt_entails_unpinned A convG convEpochs x.gPb.linksPtr hconv_len)
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (vecU8BufAt_entails_dealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot hn_le hn_lt)
      (by sep_focus) ?_
    refine seq_clean (mid := (blkPl_364).base + 1044#64)
      (P_mid := memRegion x.out 88 ∗ memRegion x.pbPtr 80 ∗
        arrayAt (chainEpoch A) 112 x.gPb.linksPtr convEpochs ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecCapPtrDealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗ A.pool ∗
        joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
        sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x20 = BitVec.ofNat 64 convEpochs.length ∧
        sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
        sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
        sm.readReg64 .x24 = x.out) ?_ ?_
    · unfold chainPBHeadersAt optChainParamsPBAt
      rw [hp]; dsimp only
      wp_steps
      have hhdr :
          (x.pbPtr ↦₆₄ x.gPb.linksCap) ∗ ((x.pbPtr + 8#64) ↦₆₄ x.gPb.linksPtr) ∗
            ((x.pbPtr + 16#64) ↦₆₄ BitVec.ofNat 64 x.pb.links.length) ∗
            ((x.pbPtr + 24#64) ↦₆₄ x.gPb.nextRoot.cap) ∗ ((x.pbPtr + 32#64) ↦₆₄ x.gPb.nextRoot.ptr) ∗
            ((x.pbPtr + 40#64) ↦₆₄ BitVec.ofNat 64 x.pb.nextRoot.length) ∗
            ((x.pbPtr + 48#64) ↦₆₄ x.pb.currentEpoch) ∗ ((x.pbPtr + 56#64) ↦₆₄ x.pb.sendEpoch) ∗
            (((x.pbPtr + 64#64) ↦₃₂ 0#32) ∗ memRegion (x.pbPtr + 64#64 + 4#64) 8) ∗
            ((x.pbPtr + 76#64) ↦₃₂ x.pb.direction) ⊢ memRegion x.pbPtr 80 := by
        have := chainPBHeadersAt_entails_memRegion_80 x.pbPtr x.gPb x.pb
        unfold chainPBHeadersAt optChainParamsPBAt at this; rw [hp] at this; exact this
      refine SepWP.focus_weaken hhdr (by sep_focus) ?_
      wp_done
    · rintro s1 hpc1 hrun1 ⟨hsp1, htr1, hfp1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1⟩
      rw [memRegion_88_words4_rest x.out]
      wp_pull_exists
      refine seq_clean (mid := (blkPl_364).base + 1100#64)
        (P_mid := chainResultAt A x.out (Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗
          memRegion x.gPb.linksPtr (convEpochs.length * 112) ∗
          linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
          vecCapPtrDealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗ A.pool ∗
          joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
          stackAt (s0.sp - 192#64) chainFromPbSubStack)
        (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
          sm.readReg64 .x19 = 0#64 ∧ sm.readReg64 .x20 = x.gPb.linksPtr ∧
          sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
          sm.readReg64 .x25 = x.gPb.linksCap) ?_ ?_
      · unfold joinScratchAt
        rw [stackAt_subStack_split_dropStack32 s0.sp]
        wp_steps
        refine SepWP.focus_weaken
          (err_stateDecode_pack_words A x.out x.pb hfromPb_eq _ _ _ (bitvec_low_byte_clear_zero _))
          (by sep_focus) ?_
        wp_call hchain_slice ⟨x.gPb.linksPtr, convEpochs⟩
        rw [hsp1]; wp_done
      · rintro s2 hpc2 hrun2 ⟨hsp2, htr2, hx19_2, hx20_2, hx21_2, hx22_2, hx25_2⟩
        exact hnone_tail s2 convEpochs sp0_val hsp0_align hpb_len hl_le hl_lt hn_lt hn_ne
          hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx25_2

set_option maxHeartbeats 800000 in
theorem fromPb_join_ok_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hchain_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 287) (dropChainEpochSliceSpec A))
    (hproto_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 288) (dropProtoEpochSliceSpec A))
    (x : ChainFromPbCall) (s0 s : State) (dir : Direction)
    (convG : List ChainEpochGhost) (convEpochs : List ChainEpoch) (sp0_val : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hdir : Direction.fromI32? x.pb.direction = some dir) (hdir_i32 : dir.toI32 = x.pb.direction)
    (hlinks : Chain.linksFromPb x.pb.links = .ok convEpochs)
    (hconv_len : convG.length = convEpochs.length) (hpb_len : convEpochs.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 792#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hx29 : s.readReg64 .fp = s0.sp - 96#64)
    (hx0 : s.readReg64 .x0 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (hx11 : s.readReg64 .x11 = x.gPb.linksPtr) (hx19 : s.readReg64 .x19 = 1#64)
    (hx20 : s.readReg64 .x20 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (hx21 : s.readReg64 .x21 = x.gPb.nextRoot.cap) (hx22 : s.readReg64 .x22 = x.gPb.nextRoot.ptr)
    (hx23 : s.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (hx24 : s.readReg64 .x24 = x.out) (hx25 : s.readReg64 .x25 = x.pbPtr) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  have h840 := @fromPb_join_ok_840_placed _ A H hdealloc hchain_slice x s0
  have hlen_lt : x.pb.links.length * 112 < 2 ^ 63 :=
    lt_of_le_of_lt (Nat.mul_le_mul_right 112 hl_le) hl_lt
  have hconv_lt : convEpochs.length * 112 < 2 ^ 63 := by rw [hpb_len]; exact hlen_lt
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  have hsub_conv := sub_links_conv_112 x.gPb.linksPtr convEpochs.length
  have hdiv_conv := div_112_magic_eq hconv_lt
  have hdiv_conv_nat := div_112_magic_nat_eq hconv_lt
  have hsub_pb := sub_links_conv_112 x.gPb.linksPtr x.pb.links.length
  have hdiv_pb := div_112_magic_eq hlen_lt
  have hdiv_pb_nat := div_112_magic_nat_eq hlen_lt
  dsimp only [dropProtoEpochSliceSpec,
    ProtoRepr.chainEpochPBSize, BitVec.ofNat_eq_ofNat] at h840 hproto_slice hpc ⊢
  refine seq_clean (mid := (blkPl_364).base + 840#64)
    (P_mid := memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
      arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
      linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
      joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x19 = 1#64 ∧
      sm.readReg64 .x20 = BitVec.ofNat 64 convEpochs.length ∧
      sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
      sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
      sm.readReg64 .x24 = x.out ∧ sm.readReg64 .x25 = x.pbPtr) ?_ ?_
  · refine SepWP.focus_weaken
      (pool_entails_empty_arrayAt_pool A (fun ep addr => ProtoRepr.chainEpochPBAt A addr ep) 112
        (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))) (by sep_focus) ?_
    rw [stackAt_subStack_split_dropStack32 s0.sp]
    wp_steps
    wp_call hproto_slice ⟨x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112), []⟩
    rw [hsp, memRegion_zero, emp_sepConj]; wp_done
  · rintro s1 hpc1 hrun1 ⟨hsp1, htr1, hfp1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1⟩
    exact h840 s1 dir convG convEpochs sp0_val hsp0_align hdir hdir_i32 hlinks hconv_len hpb_len
      hl_le hl_lt hl_ne hn_le hn_lt hn_ne hpc1 hrun1 hsp1 htr1 hfp1 hx19_1 hx20_1 hx21_1 hx22_1
      hx23_1 hx24_1 hx25_1

end CryptoVerification.SpqrV1.ChainProofs

