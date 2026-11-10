/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.Defs
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.Proof
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Verification of `spqr::chain_from` (`0x531ac`, 76 Instructions)

Proves `chainFrom_ok_of_contracts_x` and `chainFrom_ok_of_contracts_ext` for `spqr::chain_from`
(`0x531ac`) from `ChainFromPbOkX` and `ChainNewOkX`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.ChainFrom

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation.ChainFromVNNorm
open CryptoVerification.CodeLayout

gen_decodes libsignalSessionCode_tree libsignalSessionBin [0x4ddb4 → 0x4dee0]

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace ChainFromNorm

theorem chainFrom_fnOff :
    libsignalSessionCode.fnOff chainFromName = 0x4ddb4 :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) libsignalSessionCode_fnOff_0x4ddb4

theorem chainFromPb_fnOff :
    libsignalSessionCode.fnOff chainFromPbName = 0x5ac7c :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) libsignalSessionCode_fnOff_0x5ac7c

@[local simp, local arm64_norm, local wp_norm]
theorem extractLsb_lo_append64 (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 0 64 = lo := by bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem extractLsb_hi_append64 (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 64 64 = hi := by bv_kernel

theorem SepWP.rw_pre {prog : Program} {target_pc : BitVec 64} {s : State}
    {P P' : SepProp} {post : State → SepProp → Prop} (heq : P = P')
    (h : SepWP prog target_pc s P' post) :
    SepWP prog target_pc s P post :=
  heq ▸ h

theorem sp_of_imgCallInv {img : Obj.Image} {s : State} (_ : ImgCallInv img s)
    {sp' : BitVec 64} (h : s.sp = sp') : s.sp = sp' := h

theorem pointsTo32_pair_eq_pointsTo64 (a : BitVec 64) (lo hi : BitVec 32) :
    (a ↦₃₂ lo) ∗ ((a + 4#64) ↦₃₂ hi) = (a ↦₆₄ (hi ++ lo)) := by
  rw [pointsTo32_eq_pointsToBytes, pointsTo32_eq_pointsToBytes, pointsTo64_eq_pointsToBytes]
  dsimp only [unpack32, unpack64]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  have b0 : (hi ++ lo).extractLsb' 0 8 = lo.extractLsb' 0 8 := by bv_kernel
  have b1 : (hi ++ lo).extractLsb' 8 8 = lo.extractLsb' 8 8 := by bv_kernel
  have b2 : (hi ++ lo).extractLsb' 16 8 = lo.extractLsb' 16 8 := by bv_kernel
  have b3 : (hi ++ lo).extractLsb' 24 8 = lo.extractLsb' 24 8 := by bv_kernel
  have b4 : (hi ++ lo).extractLsb' 32 8 = hi.extractLsb' 0 8 := by bv_kernel
  have b5 : (hi ++ lo).extractLsb' 40 8 = hi.extractLsb' 8 8 := by bv_kernel
  have b6 : (hi ++ lo).extractLsb' 48 8 = hi.extractLsb' 16 8 := by bv_kernel
  have b7 : (hi ++ lo).extractLsb' 56 8 = hi.extractLsb' 24 8 := by bv_kernel
  rw [b0, b1, b2, b3, b4, b5, b6, b7]
  ac_rfl

/-- Split `stackAt sp chainFromStackX` into `stackAt (sp - 144#64) chainFromPbStackX` plus the
144-byte (`0x90`) local frame of `spqr::chain_from`:
- `sp - 144#64` (`+0x00`, 8B), `sp - 136#64` (`+0x08`, 8B), `sp - 128#64` (`+0x10`, 8B): temporaries
- `sp - 120#64` (`+0x18`, 88B): `Result<Chain, Error>` sret slot for `Chain::from_pb`
- `sp - 32#64` (`+0x70`, 8B), `sp - 24#64` (`+0x78`, 8B), `sp - 16#64` (`+0x80`, 8B): saved `x29, x30, x19`
- `sp - 8#64` (`+0x88`, 8B): alignment padding -/
theorem stackAt_chainFrom_split (sp : BitVec 64) :
    stackAt sp chainFromStackX =
      stackAt (sp - 144#64) chainFromPbStackX ∗
      (∃∗ g0 : BitVec 64, (sp - 144#64) ↦₆₄ g0) ∗
      (∃∗ g1 : BitVec 64, (sp - 136#64) ↦₆₄ g1) ∗
      (∃∗ g2 : BitVec 64, (sp - 128#64) ↦₆₄ g2) ∗
      memRegion (sp - 120#64) 88 ∗
      (∃∗ g3 : BitVec 64, (sp - 32#64) ↦₆₄ g3) ∗
      (∃∗ g4 : BitVec 64, (sp - 24#64) ↦₆₄ g4) ∗
      (∃∗ g5 : BitVec 64, (sp - 16#64) ↦₆₄ g5) ∗
      memRegion (sp - 8#64) 8 := by
  unfold stackAt
  have hbase : sp - 144#64 =
      sp - BitVec.ofNat 64 chainFromStackX + BitVec.ofNat 64 chainFromPbStackX := by
    change sp - 144#64 = sp - 16944#64 + 16800#64
    bv_omega
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 chainFromStackX)
      (n := chainFromPbStackX) (k := 144) (b' := sp - 144#64) (by rfl) hbase (by decide),
    ProofLib.memRegion_split' (b := sp - 144#64) (n := 8) (k := 136)
      (b' := sp - 136#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 136#64) (n := 8) (k := 128)
      (b' := sp - 128#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 128#64) (n := 8) (k := 120)
      (b' := sp - 120#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 120#64) (n := 88) (k := 32)
      (b' := sp - 32#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 32#64) (n := 8) (k := 24)
      (b' := sp - 24#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 24#64) (n := 8) (k := 16)
      (b' := sp - 16#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 16#64) (n := 8) (k := 8)
      (b' := sp - 8#64) rfl (by bv_omega) (by decide)]
  have hsub : sp - BitVec.ofNat 64 chainFromStackX =
      sp - 144#64 - BitVec.ofNat 64 chainFromPbStackX := by
    change sp - 16944#64 = sp - 144#64 - 16800#64
    bv_omega
  rw [hsub,
    ProofLib.memRegion_eight (sp - 144#64),
    ProofLib.memRegion_eight (sp - 136#64),
    ProofLib.memRegion_eight (sp - 128#64),
    ProofLib.memRegion_eight (sp - 32#64),
    ProofLib.memRegion_eight (sp - 24#64),
    ProofLib.memRegion_eight (sp - 16#64)]

theorem stackAt_chainFrom_join (sp : BitVec 64) (g0 g1 g2 g3 g4 g5 : BitVec 64) :
    stackAt (sp - 144#64) chainFromPbStackX ∗
      ((sp - 144#64) ↦₆₄ g0) ∗ ((sp - 136#64) ↦₆₄ g1) ∗ ((sp - 128#64) ↦₆₄ g2) ∗
      memRegion (sp - 120#64) 88 ∗
      ((sp - 32#64) ↦₆₄ g3) ∗ ((sp - 24#64) ↦₆₄ g4) ∗ ((sp - 16#64) ↦₆₄ g5) ∗
      memRegion (sp - 8#64) 8 ⊢
      stackAt sp chainFromStackX := by
  rw [stackAt_chainFrom_split sp]
  refine sepConj_mono_right ?_
  refine sepConj_mono (Entails.sepExists_right g0 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right g1 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right g2 (Entails.refl _)) ?_
  refine sepConj_mono_right ?_
  refine sepConj_mono (Entails.sepExists_right g3 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right g4 (Entails.refl _)) ?_
  exact sepConj_mono_left (Entails.sepExists_right g5 (Entails.refl _))

theorem stackAt_chainFrom_split_chainNew (sp : BitVec 64) :
    stackAt sp chainFromStackX =
      memRegion (sp - BitVec.ofNat 64 chainFromStackX) 336 ∗
      stackAt sp chainNewStackX := by
  unfold stackAt
  have hbase : sp - BitVec.ofNat 64 chainNewStackX =
      sp - BitVec.ofNat 64 chainFromStackX + 336#64 := by
    change sp - 16608#64 = sp - 16944#64 + 336#64
    bv_omega
  exact ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 chainFromStackX)
    (n := 336) (k := chainNewStackX) (b' := sp - BitVec.ofNat 64 chainNewStackX)
    rfl hbase (by decide)

theorem memRegion_88_words11 (out : BitVec 64) :
    memRegion out 88 =
      (∃∗ d0 : BitVec 64, out ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (out + 8#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (out + 16#64) ↦₆₄ d2) ∗
      (∃∗ d3 : BitVec 64, (out + 24#64) ↦₆₄ d3) ∗
      (∃∗ d4 : BitVec 64, (out + 32#64) ↦₆₄ d4) ∗
      (∃∗ d5 : BitVec 64, (out + 40#64) ↦₆₄ d5) ∗
      (∃∗ d6 : BitVec 64, (out + 48#64) ↦₆₄ d6) ∗
      (∃∗ d7 : BitVec 64, (out + 56#64) ↦₆₄ d7) ∗
      (∃∗ d8 : BitVec 64, (out + 64#64) ↦₆₄ d8) ∗
      (∃∗ d9 : BitVec 64, (out + 72#64) ↦₆₄ d9) ∗
      (∃∗ d10 : BitVec 64, (out + 80#64) ↦₆₄ d10) := by
  rw [ProofLib.memRegion_split' (b := out) (n := 8) (k := 80)
      (b' := out + 8#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 8#64) (n := 8) (k := 72)
      (b' := out + 16#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 16#64) (n := 8) (k := 64)
      (b' := out + 24#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 24#64) (n := 8) (k := 56)
      (b' := out + 32#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 32#64) (n := 8) (k := 48)
      (b' := out + 40#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 40#64) (n := 8) (k := 40)
      (b' := out + 48#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 48#64) (n := 8) (k := 32)
      (b' := out + 56#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 56#64) (n := 8) (k := 24)
      (b' := out + 64#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 64#64) (n := 8) (k := 16)
      (b' := out + 72#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 72#64) (n := 8) (k := 8)
      (b' := out + 80#64) rfl (by bv_omega) (by decide)]
  rw [ProofLib.memRegion_eight out,
    ProofLib.memRegion_eight (out + 8#64),
    ProofLib.memRegion_eight (out + 16#64),
    ProofLib.memRegion_eight (out + 24#64),
    ProofLib.memRegion_eight (out + 32#64),
    ProofLib.memRegion_eight (out + 40#64),
    ProofLib.memRegion_eight (out + 48#64),
    ProofLib.memRegion_eight (out + 56#64),
    ProofLib.memRegion_eight (out + 64#64),
    ProofLib.memRegion_eight (out + 72#64),
    ProofLib.memRegion_eight (out + 80#64)]

theorem words11_to_memRegion_88 (a : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
      ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗
      ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗ ((a + 64#64) ↦₆₄ w8) ∗
      ((a + 72#64) ↦₆₄ w9) ∗ ((a + 80#64) ↦₆₄ w10) ⊢
      memRegion a 88 := by
  rw [memRegion_88_words11 a]
  refine sepConj_mono (Entails.sepExists_right w0 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right w1 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right w2 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right w3 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right w4 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right w5 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right w6 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right w7 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right w8 (Entails.refl _)) ?_
  exact sepConj_mono (Entails.sepExists_right w9 (Entails.refl _))
    (Entails.sepExists_right w10 (Entails.refl _))

theorem memRegion_88_words4_rest (out : BitVec 64) :
    memRegion out 88 =
      (∃∗ d0 : BitVec 64, out ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (out + 8#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (out + 16#64) ↦₆₄ d2) ∗
      (∃∗ d3 : BitVec 64, (out + 24#64) ↦₆₄ d3) ∗
      memRegion (out + 32#64) 56 := by
  rw [ProofLib.memRegion_split' (b := out) (n := 8) (k := 80)
      (b' := out + 8#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 8#64) (n := 8) (k := 72)
      (b' := out + 16#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 16#64) (n := 8) (k := 64)
      (b' := out + 24#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 24#64) (n := 8) (k := 56)
      (b' := out + 32#64) rfl (by bv_omega) (by decide)]
  rw [ProofLib.memRegion_eight out,
    ProofLib.memRegion_eight (out + 8#64),
    ProofLib.memRegion_eight (out + 16#64),
    ProofLib.memRegion_eight (out + 24#64)]

theorem words4_rest_to_memRegion_88 (a : BitVec 64) (w0 w1 w2 w3 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
      ((a + 24#64) ↦₆₄ w3) ∗ memRegion (a + 32#64) 56 ⊢
      memRegion a 88 := by
  rw [memRegion_88_words4_rest a]
  refine sepConj_mono (Entails.sepExists_right w0 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right w1 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right w2 (Entails.refl _)) ?_
  exact sepConj_mono_left (Entails.sepExists_right w3 (Entails.refl _))

theorem word_rest72_to_memRegion_80 (a w0 : BitVec 64) :
    (a ↦₆₄ w0) ∗ memRegion (a + 8#64) 72 ⊢ memRegion a 80 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 72)
    (b' := a + 8#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_eight a]
  exact sepConj_mono_left (Entails.sepExists_right w0 (Entails.refl _))

theorem chainErrorAt_unpack_words4 (a : BitVec 64) (err : Error) :
    chainErrorAt a err =
      ∃∗ q0 : BitVec 128, ∃∗ w3 : BitVec 64,
        ⌜BitVec.truncate 8 q0 = spqrErrorTag err⌝ ∗
        (a ↦₆₄ noneCap) ∗
        ((a + 8#64) ↦₆₄ q0.extractLsb' 0 64) ∗
        ((a + 16#64) ↦₆₄ q0.extractLsb' 64 64) ∗
        ((a + 24#64) ↦₆₄ w3) ∗
        memRegion (a + 32#64) 56 := by
  unfold chainErrorAt pointsTo128
  refine congrArg sepExists (funext fun q0 => congrArg sepExists (funext fun w3 => ?_))
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

theorem chainErrorAt_pack_words4 (out : BitVec 64) (err : Error)
    (q0 : BitVec 128) (w3 : BitVec 64) (htag : BitVec.truncate 8 q0 = spqrErrorTag err) :
    (out ↦₆₄ 18446744073709551615#64) ∗
      ((out + 8#64) ↦₆₄ q0.extractLsb' 0 64) ∗
      ((out + 16#64) ↦₆₄ q0.extractLsb' 64 64) ∗
      ((out + 24#64) ↦₆₄ w3) ∗
      memRegion (out + 32#64) 56 ⊢
      chainErrorAt out err := by
  rw [chainErrorAt_unpack_words4 out err]
  refine Entails.sepExists_right q0 (Entails.sepExists_right w3 ?_)
  exact Entails.pure_right htag (Entails.refl _)

/-- Heap and pure invariant part of `chainAt A a G c` (independent of address `a`). -/
def chainAtHeap (A : RustAlloc) (G : ChainGhost) (c : Chain) : SepProp :=
  ⌜G.epochs.length = c.links.length⌝ ∗
    vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A)
      G.linksCap G.linksPtr G.linksHead (G.epochs.zip c.links) ∗
    ⌜c.nextRoot.length ≤ G.nextRoot.cap.toNat ∧
      G.nextRoot.cap.toNat < 2 ^ 63 ∧ G.nextRoot.ptr ≠ 0⌝ ∗
    (if G.nextRoot.cap = 0 then emp
     else A.live G.nextRoot.ptr G.nextRoot.cap.toNat 1 ∗
       (G.nextRoot.ptr ↦ₛ c.nextRoot) ∗
       memRegion (G.nextRoot.ptr + BitVec.ofNat 64 c.nextRoot.length)
         (G.nextRoot.cap.toNat - c.nextRoot.length))

theorem vecDequeRingBuf_linksCap_ne_noneCap (A : RustAlloc) (cap ptr head : BitVec 64)
    (xs : List (ChainEpochGhost × ChainEpoch)) :
    vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A) cap ptr head xs ⊢
      ⌜cap ≠ noneCap⌝ ∗
      vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A) cap ptr head xs := by
  unfold vecDequeRingBuf
  refine Entails.pure_left fun hp => ?_
  have hne : cap ≠ noneCap := by
    have hlt : cap.toNat * 112 < 2 ^ 63 := hp.2.1
    intro heq; rw [heq] at hlt
    change 0xFFFFFFFFFFFFFFFF * 112 < 2 ^ 63 at hlt
    omega
  exact Entails.pure_right hne (Entails.pure_right hp (Entails.refl _))

theorem chainRepr_entails_words11 (A : RustAlloc) (a : BitVec 64) (c : Chain) :
    chainRepr A a c ⊢
      ∃∗ G : ChainGhost, ∃∗ pad : BitVec 32,
        ⌜G.linksCap ≠ noneCap⌝ ∗
        (a ↦₆₄ G.linksCap) ∗
        ((a + 8#64) ↦₆₄ G.linksPtr) ∗
        ((a + 16#64) ↦₆₄ G.linksHead) ∗
        ((a + 24#64) ↦₆₄ BitVec.ofNat 64 (G.epochs.zip c.links).length) ∗
        ((a + 32#64) ↦₆₄ G.nextRoot.cap) ∗
        ((a + 40#64) ↦₆₄ G.nextRoot.ptr) ∗
        ((a + 48#64) ↦₆₄ BitVec.ofNat 64 c.nextRoot.length) ∗
        ((a + 56#64) ↦₆₄ c.currentEpoch) ∗
        ((a + 64#64) ↦₆₄ c.sendEpoch) ∗
        ((a + 72#64) ↦₆₄ (c.params.maxOooKeys ++ c.params.maxJump)) ∗
        ((a + 80#64) ↦₆₄ (pad ++ c.dir.toI32)) ∗
        chainAtHeap A G c := by
  unfold chainRepr
  refine Entails.sepExists_elim fun G => ?_
  unfold chainAt vecDequeAt vecDequeHeader vecU8At vecHeader chainParamsAt directionAt chainAtHeap
  rw [ProofLib.memRegion_four (a + 0x54#64)]
  simp only [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun pad => ?_
  refine Entails.sepExists_right G (Entails.sepExists_right pad ?_)
  have hp72 :
      ((a + 0x48#64) ↦₃₂ c.params.maxJump) ∗ ((a + 0x48#64 + 0x04#64) ↦₃₂ c.params.maxOooKeys) =
        ((a + 72#64) ↦₆₄ (c.params.maxOooKeys ++ c.params.maxJump)) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      pointsTo32_pair_eq_pointsTo64 (a + 72#64) c.params.maxJump c.params.maxOooKeys
  have hp80 :
      ((a + 0x50#64) ↦₃₂ c.dir.toI32) ∗ ((a + 0x54#64) ↦₃₂ pad) =
        ((a + 80#64) ↦₆₄ (pad ++ c.dir.toI32)) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      pointsTo32_pair_eq_pointsTo64 (a + 80#64) c.dir.toI32 pad
  have h1 :
      ⌜G.epochs.length = c.links.length⌝ ∗
        ((a ↦₆₄ G.linksCap ∗ (a + 0x08#64) ↦₆₄ G.linksPtr ∗ (a + 0x10#64) ↦₆₄ G.linksHead ∗
            (a + 0x18#64) ↦₆₄ BitVec.ofNat 64 (G.epochs.zip c.links).length) ∗
          vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A) G.linksCap G.linksPtr
            G.linksHead (G.epochs.zip c.links)) ∗
        (((a + 0x20#64) ↦₆₄ G.nextRoot.cap ∗ (a + 0x20#64 + 8#64) ↦₆₄ G.nextRoot.ptr ∗
            (a + 0x20#64 + 16#64) ↦₆₄ BitVec.ofNat 64 c.nextRoot.length) ∗
          ⌜c.nextRoot.length ≤ G.nextRoot.cap.toNat ∧
              G.nextRoot.cap.toNat < 2 ^ 63 ∧ G.nextRoot.ptr ≠ 0⌝ ∗
            if G.nextRoot.cap = 0 then emp
            else
              A.live G.nextRoot.ptr G.nextRoot.cap.toNat 1 ∗ G.nextRoot.ptr ↦ₛ c.nextRoot ∗
                memRegion (G.nextRoot.ptr + BitVec.ofNat 64 c.nextRoot.length)
                  (G.nextRoot.cap.toNat - c.nextRoot.length)) ∗
        (a + 0x38#64) ↦₆₄ c.currentEpoch ∗ (a + 0x40#64) ↦₆₄ c.sendEpoch ∗
        ((a + 0x48#64) ↦₃₂ c.params.maxJump ∗ (a + 0x48#64 + 0x04#64) ↦₃₂ c.params.maxOooKeys) ∗
        (a + 0x50#64) ↦₃₂ c.dir.toI32 ∗ (a + 0x54#64) ↦₃₂ pad =
      vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A) G.linksCap G.linksPtr
          G.linksHead (G.epochs.zip c.links) ∗
        ((a ↦₆₄ G.linksCap) ∗
          ((a + 8#64) ↦₆₄ G.linksPtr) ∗
          ((a + 16#64) ↦₆₄ G.linksHead) ∗
          ((a + 24#64) ↦₆₄ BitVec.ofNat 64 (G.epochs.zip c.links).length) ∗
          ((a + 32#64) ↦₆₄ G.nextRoot.cap) ∗
          ((a + 40#64) ↦₆₄ G.nextRoot.ptr) ∗
          ((a + 48#64) ↦₆₄ BitVec.ofNat 64 c.nextRoot.length) ∗
          ((a + 56#64) ↦₆₄ c.currentEpoch) ∗
          ((a + 64#64) ↦₆₄ c.sendEpoch) ∗
          ((a + 72#64) ↦₆₄ (c.params.maxOooKeys ++ c.params.maxJump)) ∗
          ((a + 80#64) ↦₆₄ (pad ++ c.dir.toI32)) ∗
          ⌜G.epochs.length = c.links.length⌝ ∗
          ⌜c.nextRoot.length ≤ G.nextRoot.cap.toNat ∧
              G.nextRoot.cap.toNat < 2 ^ 63 ∧ G.nextRoot.ptr ≠ 0⌝ ∗
          (if G.nextRoot.cap = 0 then emp
           else
             A.live G.nextRoot.ptr G.nextRoot.cap.toNat 1 ∗ G.nextRoot.ptr ↦ₛ c.nextRoot ∗
               memRegion (G.nextRoot.ptr + BitVec.ofNat 64 c.nextRoot.length)
                 (G.nextRoot.cap.toNat - c.nextRoot.length))) := by
    rw [hp72, hp80]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    ac_rfl
  rw [h1]
  refine Entails.trans
    (sepConj_mono_left (vecDequeRingBuf_linksCap_ne_noneCap A G.linksCap G.linksPtr G.linksHead
      (G.epochs.zip c.links))) ?_
  exact Entails.of_eq (by ac_rfl)

theorem words11_entails_chainRepr (A : RustAlloc) (out : BitVec 64) (G : ChainGhost) (c : Chain)
    (pad : BitVec 32) :
    (out ↦₆₄ G.linksCap) ∗
      ((out + 8#64) ↦₆₄ G.linksPtr) ∗
      ((out + 16#64) ↦₆₄ G.linksHead) ∗
      ((out + 24#64) ↦₆₄ BitVec.ofNat 64 (G.epochs.zip c.links).length) ∗
      ((out + 32#64) ↦₆₄ G.nextRoot.cap) ∗
      ((out + 40#64) ↦₆₄ G.nextRoot.ptr) ∗
      ((out + 48#64) ↦₆₄ BitVec.ofNat 64 c.nextRoot.length) ∗
      ((out + 56#64) ↦₆₄ c.currentEpoch) ∗
      ((out + 64#64) ↦₆₄ c.sendEpoch) ∗
      ((out + 72#64) ↦₆₄ (c.params.maxOooKeys ++ c.params.maxJump)) ∗
      ((out + 80#64) ↦₆₄ (pad ++ c.dir.toI32)) ∗
      chainAtHeap A G c ⊢
      chainRepr A out c := by
  unfold chainRepr
  refine Entails.sepExists_right G ?_
  unfold chainAt vecDequeAt vecDequeHeader vecU8At vecHeader chainParamsAt directionAt chainAtHeap
  have hp72 :
      ((out + 72#64) ↦₆₄ (c.params.maxOooKeys ++ c.params.maxJump)) =
        ((out + 0x48#64) ↦₃₂ c.params.maxJump) ∗ ((out + 0x48#64 + 0x04#64) ↦₃₂ c.params.maxOooKeys) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      (pointsTo32_pair_eq_pointsTo64 (out + 72#64) c.params.maxJump c.params.maxOooKeys).symm
  have hp80 :
      ((out + 80#64) ↦₆₄ (pad ++ c.dir.toI32)) =
        ((out + 0x50#64) ↦₃₂ c.dir.toI32) ∗ ((out + 0x54#64) ↦₃₂ pad) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      (pointsTo32_pair_eq_pointsTo64 (out + 80#64) c.dir.toI32 pad).symm
  rw [hp72, hp80]
  have hpad : ((out + 0x54#64) ↦₃₂ pad) ⊢ memRegion (out + 0x54#64) 4 := by
    rw [ProofLib.memRegion_four (out + 0x54#64)]
    exact Entails.sepExists_right pad (Entails.refl _)
  rw [show
    (out ↦₆₄ G.linksCap) ∗
      ((out + 8#64) ↦₆₄ G.linksPtr) ∗
      ((out + 16#64) ↦₆₄ G.linksHead) ∗
      ((out + 24#64) ↦₆₄ BitVec.ofNat 64 (G.epochs.zip c.links).length) ∗
      ((out + 32#64) ↦₆₄ G.nextRoot.cap) ∗
      ((out + 40#64) ↦₆₄ G.nextRoot.ptr) ∗
      ((out + 48#64) ↦₆₄ BitVec.ofNat 64 c.nextRoot.length) ∗
      ((out + 56#64) ↦₆₄ c.currentEpoch) ∗
      ((out + 64#64) ↦₆₄ c.sendEpoch) ∗
      (((out + 0x48#64) ↦₃₂ c.params.maxJump) ∗ ((out + 0x48#64 + 0x04#64) ↦₃₂ c.params.maxOooKeys)) ∗
      (((out + 0x50#64) ↦₃₂ c.dir.toI32) ∗ ((out + 0x54#64) ↦₃₂ pad)) ∗
      (⌜G.epochs.length = c.links.length⌝ ∗
        vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A) G.linksCap G.linksPtr
          G.linksHead (G.epochs.zip c.links) ∗
        ⌜c.nextRoot.length ≤ G.nextRoot.cap.toNat ∧
            G.nextRoot.cap.toNat < 2 ^ 63 ∧ G.nextRoot.ptr ≠ 0⌝ ∗
        if G.nextRoot.cap = 0 then emp
        else
          A.live G.nextRoot.ptr G.nextRoot.cap.toNat 1 ∗ G.nextRoot.ptr ↦ₛ c.nextRoot ∗
            memRegion (G.nextRoot.ptr + BitVec.ofNat 64 c.nextRoot.length)
              (G.nextRoot.cap.toNat - c.nextRoot.length)) =
    ⌜G.epochs.length = c.links.length⌝ ∗
      ((out ↦₆₄ G.linksCap ∗ (out + 0x08#64) ↦₆₄ G.linksPtr ∗ (out + 0x10#64) ↦₆₄ G.linksHead ∗
          (out + 0x18#64) ↦₆₄ BitVec.ofNat 64 (G.epochs.zip c.links).length) ∗
        vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A) G.linksCap G.linksPtr
          G.linksHead (G.epochs.zip c.links)) ∗
      (((out + 0x20#64) ↦₆₄ G.nextRoot.cap ∗ (out + 0x20#64 + 8#64) ↦₆₄ G.nextRoot.ptr ∗
          (out + 0x20#64 + 16#64) ↦₆₄ BitVec.ofNat 64 c.nextRoot.length) ∗
        ⌜c.nextRoot.length ≤ G.nextRoot.cap.toNat ∧
            G.nextRoot.cap.toNat < 2 ^ 63 ∧ G.nextRoot.ptr ≠ 0⌝ ∗
          if G.nextRoot.cap = 0 then emp
          else
            A.live G.nextRoot.ptr G.nextRoot.cap.toNat 1 ∗ G.nextRoot.ptr ↦ₛ c.nextRoot ∗
              memRegion (G.nextRoot.ptr + BitVec.ofNat 64 c.nextRoot.length)
                (G.nextRoot.cap.toNat - c.nextRoot.length)) ∗
      (out + 0x38#64) ↦₆₄ c.currentEpoch ∗ (out + 0x40#64) ↦₆₄ c.sendEpoch ∗
      ((out + 0x48#64) ↦₃₂ c.params.maxJump ∗ (out + 0x48#64 + 0x04#64) ↦₃₂ c.params.maxOooKeys) ∗
      (out + 0x50#64) ↦₃₂ c.dir.toI32 ∗ ((out + 0x54#64) ↦₃₂ pad) by
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      ac_rfl]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right hpad))))))

def chainPBRestAt (A : RustAlloc) (g : ChainPBGhost) (a : BitVec 64) (pb : ChainPB) : SepProp :=
  ⌜g.epochs.length = pb.links.length⌝ ∗
    ((a + 8#64) ↦₆₄ g.linksPtr) ∗
    ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (g.epochs.zip pb.links).length) ∗
    vecBuf A chainEpochSize chainEpochAlign (chainEpochPBAt A)
      g.linksCap g.linksPtr (g.epochs.zip pb.links) ∗
    vecU8At A (a + 0x18#64) g.nextRoot.cap g.nextRoot.ptr pb.nextRoot ∗
    ((a + 0x30#64) ↦₆₄ pb.currentEpoch) ∗
    ((a + 0x38#64) ↦₆₄ pb.sendEpoch) ∗
    optChainParamsPBAt (a + 0x40#64) pb.params ∗
    ((a + 0x4c#64) ↦₃₂ pb.direction)

theorem vecBuf_linksCap_ne_noneCap (A : RustAlloc) (cap ptr : BitVec 64)
    (xs : List (ChainEpochPBGhost × ChainEpochPB)) :
    vecBuf A chainEpochSize chainEpochAlign (chainEpochPBAt A) cap ptr xs ⊢
      ⌜cap ≠ noneCap⌝ ∗
      vecBuf A chainEpochSize chainEpochAlign (chainEpochPBAt A) cap ptr xs := by
  unfold vecBuf
  refine Entails.pure_left fun hp => ?_
  have hne : cap ≠ noneCap := by
    have hlt : cap.toNat * 112 < 2 ^ 63 := hp.2.1
    intro heq; rw [heq] at hlt
    change 0xFFFFFFFFFFFFFFFF * 112 < 2 ^ 63 at hlt
    omega
  exact Entails.pure_right hne (Entails.pure_right hp (Entails.refl _))

theorem chainPBAt_expose_cap (A : RustAlloc) (g : ChainPBGhost) (a : BitVec 64) (pb : ChainPB) :
    chainPBAt A g a pb ⊢
      ⌜g.linksCap ≠ noneCap⌝ ∗ (a ↦₆₄ g.linksCap) ∗ chainPBRestAt A g a pb := by
  unfold chainPBAt vecAt vecHeader chainPBRestAt
  rw [show
    ⌜g.epochs.length = pb.links.length⌝ ∗
      ((a ↦₆₄ g.linksCap ∗ (a + 8#64) ↦₆₄ g.linksPtr ∗
          (a + 16#64) ↦₆₄ BitVec.ofNat 64 (g.epochs.zip pb.links).length) ∗
        vecBuf A chainEpochSize chainEpochAlign (chainEpochPBAt A)
          g.linksCap g.linksPtr (g.epochs.zip pb.links)) ∗
      vecU8At A (a + 0x18#64) g.nextRoot.cap g.nextRoot.ptr pb.nextRoot ∗
      (a + 0x30#64) ↦₆₄ pb.currentEpoch ∗
      (a + 0x38#64) ↦₆₄ pb.sendEpoch ∗
      optChainParamsPBAt (a + 0x40#64) pb.params ∗
      (a + 0x4c#64) ↦₃₂ pb.direction =
    vecBuf A chainEpochSize chainEpochAlign (chainEpochPBAt A)
        g.linksCap g.linksPtr (g.epochs.zip pb.links) ∗
      ((a ↦₆₄ g.linksCap) ∗
        (⌜g.epochs.length = pb.links.length⌝ ∗
          ((a + 8#64) ↦₆₄ g.linksPtr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (g.epochs.zip pb.links).length) ∗
          vecU8At A (a + 0x18#64) g.nextRoot.cap g.nextRoot.ptr pb.nextRoot ∗
          ((a + 0x30#64) ↦₆₄ pb.currentEpoch) ∗
          ((a + 0x38#64) ↦₆₄ pb.sendEpoch) ∗
          optChainParamsPBAt (a + 0x40#64) pb.params ∗
          ((a + 0x4c#64) ↦₃₂ pb.direction))) by ac_rfl]
  refine Entails.trans
    (sepConj_mono_left (vecBuf_linksCap_ne_noneCap A g.linksCap g.linksPtr (g.epochs.zip pb.links))) ?_
  exact Entails.of_eq (by ac_rfl)

theorem chainPBAt_unexpose_cap (A : RustAlloc) (g : ChainPBGhost) (a : BitVec 64) (pb : ChainPB) :
    (a ↦₆₄ g.linksCap) ∗ chainPBRestAt A g a pb ⊢ chainPBAt A g a pb := by
  unfold chainPBAt vecAt vecHeader chainPBRestAt
  exact Entails.of_eq (by ac_rfl)

theorem add_one_beq_zero_of_ne_noneCap {c : BitVec 64} (hne : c ≠ noneCap) :
    (c + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  apply hne
  change c = 0#64 - 1#64
  rw [← heq]
  bv_omega

/-- Framed `BL` call rule for `SepWPp` with an `.inImage img` callee contract and a `SepWP`
return continuation. -/
theorem SepWPp.call_frame_inImage_ret {α : Type} {prog : Program} {img : Obj.Image}
    {entry callee_ret_pc caller_ret_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (x : α) {s : State} {φ : Prop} {P T F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hF : ImgCallInv img s)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = callee_ret_pc)
    (hspec : spec.pre x s = ⌜φ⌝ ∗ T)
    (hφ : φ)
    (hP : P = T ∗ F)
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl)
    (hnext : ∀ sf : State, sf.pc = callee_ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWP prog caller_ret_pc sf (spec.post x s sf ∗ F) post) :
    SepWPp prog caller_ret_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) :=
  ProofLib.SepWPp.call_wpp_frozen (x := x) (F := F) hcall hF.1 hF.2 hpc hrun hsp_align hlr
    (fun R' hm => by
      dsimp only [Spec.inImage]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hF.1, hF.2⟩, ?_⟩
      rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
      exact ⟨hφ, hm⟩)
    (fun sf code _ _ hex => by
      dsimp only [Spec.inImage] at hex
      rw [hexit_eq] at hex
      exact not_satisfies_false_sepConj hex)
    (fun sf _ _ hm' => Satisfies.mono (sepConj_mono_left (hpan sf)) hm')
    (fun sf hpcm hrunm hspm hcsm _ _ => ProofLib.SepWPp.of_sepWP_ret (hnext sf hpcm hrunm hspm hcsm))
    (fun sf R' _ hoom => by
      dsimp only [Spec.inImage] at hoom
      rw [hoom_eq] at hoom
      exact (not_satisfies_false_sepConj hoom).elim)

end ChainFromNorm

open ChainFromNorm

ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
  ult_one_toI32
  extractLsb_lo_append64 extractLsb_hi_append64
  chainFrom_fnOff chainFromPb_fnOff chainNew_fnOff
  libsignalSessionCode_fnOff_0x4ddb4
  libsignalSessionCode_fnOff_0x5ac7c
  libsignalSessionCode_fnOff_0x5aaac

macro "wp_elim_exists" : tactic =>
  `(tactic| repeat' (first | (apply SepWPp.exists_elim; intro _) | (apply SepWP.exists_elim; intro _)))

set_option maxHeartbeats 1600000 in
/-- `spqr::chain_from` (`0x531ac`, 76 instructions) meets `(chainFromSpecX hkdf A).inImage img`
on `tripleRatchetProgAtExt img.base ext` assuming `ChainFromPbOkX img A ext` and
`ChainNewOkX img hkdf A ext`. -/
theorem chainFrom_ok_of_contracts_x {img : Obj.Image} {hkdf : HkdfFn}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hpb : ChainFromPbOkX img A ext)
    (hnew : ChainNewOkX img hkdf A ext) :
    ChainFromOkX img hkdf A ext := by
  unfold ChainFromOkX tripleRatchetProgAtExt
  wpp_init x s0
  have hfn : libsignalSessionCode.fnOff chainFromName = 0x4ddb4 := chainFrom_fnOff
  code_fetches libsignalSessionCode libsignalSessionBin img.base
    (Rust.withPanics ext) hfn 0x4ddb4 304
  have h_from_pb := sub_ok_at_rebase (name := chainFromName) (callee := chainFromPbName)
    (k := num% (0x5ac7c - 0x4ddb4)) (by rw [chainFrom_fnOff, chainFromPb_fnOff]) hpb
  have h_new := sub_ok_at_rebase (name := chainFromName) (callee := chainNewName)
    (k := num% (0x5aaac - 0x4ddb4)) (by rw [chainFrom_fnOff, chainNew_fnOff]) hnew
  replace hpc : s0.pc =
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainFromName :=
    hpc.trans (by rw [Program.fnAddr_rebase, hfn])
  clear hpb hnew hfn
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainFromName = entry
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  rcases x with ⟨out, pbPtr, vnOptPtr, gPb, vnPin, pb, vn⟩
  have hinv0 : ImgCallInv img s0 := ⟨h_2, h_1⟩
  subst h_4 h_3 h
  refine SepWPp.rw_pre (by
    simp only [stackAt_chainFrom_split s0.sp,
      sepExists_sepConj_left, sepExists_sepConj_right]
    rfl) ?_
  wp_elim_exists
  cases pb with
  | some chainPb =>
    have hcf_eq : chainFrom hkdf (some chainPb) vn = Chain.fromPb chainPb := rfl
    dsimp only [optChainPBAt]
    refine SepWPp.fold (chainPBAt_expose_cap A gPb (s0.readReg64 (.gpr 1#5)) chainPb)
      (by sep_focus) ?_
    refine SepWPp.pure_left_focus _ (by sep_focus) fun hcap_ne => ?_
    have hz_cap : (gPb.linksCap + 1#64 == 0#64) = false := add_one_beq_zero_of_ne_noneCap hcap_ne
    refine SepWPp.of_sepWP_inImage (mid := entry + bv% (0x5ac7c - 0x4ddb4)) hinv0 ?_
    wp_steps
    refine SepWP.fold (chainPBAt_unexpose_cap A gPb (s0.readReg64 (.gpr 1#5)) chainPb)
      (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    apply (SepWPp.call_frame_inImage_ret h_from_pb
      (⟨s0.sp - 120#64, s0.readReg64 (.gpr 1#5), gPb, chainPb⟩ : ChainFromPbCall)
      hinv1 (callee_ret_pc := entry + 44#64))
    · wp_focus_close wp_norm_goal
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · rfl
    · refine ⟨by wp_norm_lhs, by wp_norm_lhs⟩
    · rw [sp_of_imgCallInv hinv1 (sp' := s0.sp - 144#64) (by wp_norm_lhs)]
      sep_focus
    · intro sf
      exact onPanic_entails_of_trace_eq (by wp_norm_lhs)
    · intro _ _; rfl
    · intro sf hpc_sf hrun_sf hsp_sf hcs_sf
      dsimp only [chainFromPbSpecX]
      have hsp_sf' : sf.sp = s0.sp - 144#64 := hsp_sf.trans (by wp_norm_lhs)
      have hx19_sf : sf.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 0#5) :=
        hcs_sf.1.trans (by wp_norm_lhs)
      rw [sp_of_imgCallInv hinv1 (sp' := s0.sp - 144#64) (by wp_norm_lhs)]
      refine SepWP.focus_pure (by sep_focus) fun htr_sf => ?_
      rw [hcf_eq]
      cases hres : Chain.fromPb chainPb with
      | ok ch =>
        dsimp only [chainResultAt]
        refine SepWP.fold (chainRepr_entails_words11 A (s0.sp - 120#64) ch)
          (by sep_focus) ?_
        refine SepWP.rw_pre (by
          simp only [sepExists_sepConj_left, sepConj_assoc]
          rfl) ?_
        apply SepWP.exists_elim; intro G
        apply SepWP.exists_elim; intro pad
        refine SepWP.focus_pure (by sep_focus) fun hcap_ch_ne => ?_
        have hz_ch : (G.linksCap + 1#64 == 0#64) = false := add_one_beq_zero_of_ne_noneCap hcap_ch_ne
        refine SepWP.rw_pre (by
          simp only [memRegion_88_words11 (s0.readReg64 (.gpr 0#5)),
            sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
          rfl) ?_
        wp_elim_exists
        wp_steps
        refine SepWP.fold (words11_entails_chainRepr A (s0.readReg64 (.gpr 0#5)) G ch pad)
          (by sep_focus) ?_
        refine SepWP.fold (words11_to_memRegion_88 (s0.sp - 120#64)
          G.linksCap G.linksPtr G.linksHead (BitVec.ofNat 64 (G.epochs.zip ch.links).length)
          G.nextRoot.cap G.nextRoot.ptr (BitVec.ofNat 64 ch.nextRoot.length)
          ch.currentEpoch ch.sendEpoch (ch.params.maxOooKeys ++ ch.params.maxJump)
          (pad ++ ch.dir.toI32)) (by sep_focus) ?_
        refine SepWP.fold (stackAt_chainFrom_join s0.sp _ _ _ _ _ _) (by sep_focus) ?_
        wp_done
      | error err =>
        dsimp only [chainResultAt]
        refine SepWP.rw_pre (by
          simp only [chainErrorAt_unpack_words4 (s0.sp - 120#64) err,
            sepExists_sepConj_left, sepConj_assoc]
          rfl) ?_
        apply SepWP.exists_elim; intro q0_err
        apply SepWP.exists_elim; intro w3_err
        refine SepWP.rw_pre (by
          simp only [memRegion_88_words4_rest (s0.readReg64 (.gpr 0#5)),
            sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
          rfl) ?_
        wp_elim_exists
        refine SepWP.focus_pure (by sep_focus) fun htag_q0 => ?_
        refine SepWP.rw_pre (by simp only [noneCap]; rfl) ?_
        wp_steps
        refine SepWP.fold (chainErrorAt_pack_words4 (s0.readReg64 (.gpr 0#5)) err q0_err w3_err htag_q0)
          (by sep_focus) ?_
        refine SepWP.fold (words4_rest_to_memRegion_88 (s0.sp - 120#64)
          18446744073709551615#64 (q0_err.extractLsb' 0 64) (q0_err.extractLsb' 64 64) w3_err)
          (by sep_focus) ?_
        refine SepWP.fold (stackAt_chainFrom_join s0.sp _ _ _ _ _ _) (by sep_focus) ?_
        wp_done
  | none =>
    dsimp only [optChainPBAt, noneCap]
    cases vn with
    | none =>
      have hcf_eq : chainFrom hkdf none none = .error .chainNotAvailable := rfl
      dsimp only [optVersionNegotiationRefAt]
      refine SepWPp.pure_left_focus _ (by sep_focus) fun hvn0 => ?_
      refine SepWPp.rw_pre (by
        simp only [memRegion_88_err_split (s0.readReg64 (.gpr 0#5)),
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        rfl) ?_
      apply SepWPp.exists_elim; intro w2_out
      apply SepWPp.exists_elim; intro w1_out
      apply SepWPp.exists_elim; intro bs7_out
      apply SepWPp.exists_elim; intro b0_out
      apply SepWPp.exists_elim; intro w0_out
      refine SepWPp.pure_left_focus _ (by sep_focus) fun hbs7 => ?_
      apply SepWPp.of_sepWP_ret
      wp_steps
      rw [hcf_eq]
      dsimp only [chainResultAt]
      refine SepWP.fold (fold_chainErrorAt (s0.readReg64 (.gpr 0#5)) .chainNotAvailable 15#8 rfl hbs7 w1_out w2_out)
        (by sep_focus) ?_
      refine SepWP.fold (word_rest72_to_memRegion_80 (s0.readReg64 (.gpr 1#5)) 18446744073709551615#64)
        (by sep_focus) ?_
      refine SepWP.fold (stackAt_chainFrom_join s0.sp _ _ _ _ _ _) (by sep_focus) ?_
      wp_done
    | some v =>
      dsimp only [optVersionNegotiationRefAt, versionNegotiationPBAt]
      refine SepWPp.pure_left_focus _ (by sep_focus) fun hvn_ne => ?_
      rcases direction_fromI32_or v.direction with
        ⟨dir, hdir_val, hdir_opt, hcond_hi⟩ | ⟨hdir_opt, hcond_hi⟩
      · cases hcp : v.chainParams with
        | none =>
          have hcf_eq : chainFrom hkdf none (some v) = .error .chainNotAvailable := by
            simp [chainFrom, chainFromVersionNegotiation, hdir_opt, hcp]; rfl
          dsimp only [optChainParamsPBAt]
          refine SepWPp.rw_pre (by
            simp only [memRegion_88_err_split (s0.readReg64 (.gpr 0#5)),
              sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
            rfl) ?_
          apply SepWPp.exists_elim; intro w2_out
          apply SepWPp.exists_elim; intro w1_out
          apply SepWPp.exists_elim; intro bs7_out
          apply SepWPp.exists_elim; intro b0_out
          apply SepWPp.exists_elim; intro w0_out
          refine SepWPp.pure_left_focus _ (by sep_focus) fun hbs7 => ?_
          apply SepWPp.of_sepWP_ret
          wp_steps
          rw [hcf_eq]
          dsimp only [chainResultAt]
          refine SepWP.fold (fold_chainErrorAt (s0.readReg64 (.gpr 0#5)) .chainNotAvailable 15#8 rfl hbs7 w1_out w2_out)
            (by sep_focus) ?_
          refine SepWP.fold (word_rest72_to_memRegion_80 (s0.readReg64 (.gpr 1#5)) 18446744073709551615#64)
            (by sep_focus) ?_
          refine SepWP.fold (stackAt_chainFrom_join s0.sp _ _ _ _ _ _) (by sep_focus) ?_
          wp_done
        | some cp =>
          have hcf_eq : chainFrom hkdf none (some v) =
              .ok (chainNewVal hkdf v.authKey dir cp) := by
            simp [chainFrom, chainFromVersionNegotiation, hdir_opt, hcp]; rfl
          dsimp only [optChainParamsPBAt]
          refine SepWPp.fold (vecU8At_entails_header_bytesAt_rest A
            (s0.readReg64 (.gpr 2#5)) vnPin.cap vnPin.ptr v.authKey) (by sep_focus) ?_
          refine SepWPp.pure_left_focus _ (by sep_focus) fun hlen64 => ?_
          refine SepWPp.of_sepWP_inImage (mid := entry + bv% (0x5aaac - 0x4ddb4)) hinv0 ?_
          wp_steps
          refine SepWP.fold (word_rest72_to_memRegion_80 (s0.readReg64 (.gpr 1#5)) 18446744073709551615#64)
            (by sep_focus) ?_
          refine SepWP.fold (stackAt_chainFrom_join s0.sp _ _ _ _ _ _) (by sep_focus) ?_
          refine SepWP.rw_pre (by
            simp only [stackAt_chainFrom_split_chainNew s0.sp, sepConj_assoc]
            rfl) ?_
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          intro hinv1
          apply (SepWPp.tail_call_frame_inImage h_new
            (⟨s0.readReg64 (.gpr 0#5), false, vnPin.ptr, v.authKey, dir, cp⟩ : ChainNewGhost)
            hinv1)
          · wp_focus_close wp_norm_goal
          · wp_focus_close wp_norm_lhs
          · wp_focus_close wp_norm_lhs
          · wp_focus_close wp_norm_lhs
          · rfl
          · refine ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hlen64⟩
          · rw [sp_of_imgCallInv hinv1 (sp' := s0.sp) (by wp_norm_lhs)]
            sep_focus
          · intro sf
            exact onPanic_entails_of_trace_eq (by wp_norm_lhs)
          · intro _ _; rfl
          · intro sf hpc_sf hrun_sf hsp_sf hcs_sf
            dsimp only [chainNewSpecX]
            rw [sp_of_imgCallInv hinv1 (sp' := s0.sp) (by wp_norm_lhs)]
            refine SepWP.focus_pure (by sep_focus) fun htr_sf => ?_
            rw [hcf_eq]
            dsimp only [chainResultAt]
            refine SepWP.fold (chainNew_post_entails_chainRepr A (s0.readReg64 (.gpr 0#5)) _)
              (by sep_focus) ?_
            refine SepWP.fold (header_bytesAt_rest_entails_vecU8At A
              (s0.readReg64 (.gpr 2#5)) vnPin.cap vnPin.ptr v.authKey) (by sep_focus) ?_
            refine SepWP.fold (Entails.of_eq (stackAt_chainFrom_split_chainNew s0.sp).symm)
              (by sep_focus) ?_
            wp_done
      · have hcf_eq : chainFrom hkdf none (some v) = .error .stateDecode := by
          simp [chainFrom, chainFromVersionNegotiation, hdir_opt]; rfl
        refine SepWPp.rw_pre (by
          simp only [memRegion_88_err_split (s0.readReg64 (.gpr 0#5)),
            sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
          rfl) ?_
        apply SepWPp.exists_elim; intro w2_out
        apply SepWPp.exists_elim; intro w1_out
        apply SepWPp.exists_elim; intro bs7_out
        apply SepWPp.exists_elim; intro b0_out
        apply SepWPp.exists_elim; intro w0_out
        refine SepWPp.pure_left_focus _ (by sep_focus) fun hbs7 => ?_
        apply SepWPp.of_sepWP_ret
        wp_steps
        rw [hcf_eq]
        dsimp only [chainResultAt]
        refine SepWP.fold (fold_chainErrorAt (s0.readReg64 (.gpr 0#5)) .stateDecode 0#8 rfl hbs7 w1_out w2_out)
          (by sep_focus) ?_
        refine SepWP.fold (word_rest72_to_memRegion_80 (s0.readReg64 (.gpr 1#5)) 18446744073709551615#64)
          (by sep_focus) ?_
        refine SepWP.fold (stackAt_chainFrom_join s0.sp _ _ _ _ _ _) (by sep_focus) ?_
        wp_done

private theorem stackAt_chainFromExt_split_x (sp : BitVec 64) :
    stackAt sp chainFromStackExt =
      memRegion (sp - BitVec.ofNat 64 chainFromStackExt) 1232 ∗ stackAt sp chainFromStackX := by
  unfold stackAt
  have hbase : sp - BitVec.ofNat 64 chainFromStackX =
      sp - BitVec.ofNat 64 chainFromStackExt + 1232#64 := by
    change sp - 16944#64 = sp - 18176#64 + 1232#64; bv_omega
  exact ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 chainFromStackExt)
    (n := 1232) (k := chainFromStackX) (b' := sp - BitVec.ofNat 64 chainFromStackX)
    rfl hbase (by decide)

private theorem stackAt_chainFromExt_split_chainNewExt (sp : BitVec 64) :
    stackAt sp chainFromStackExt =
      memRegion (sp - BitVec.ofNat 64 chainFromStackExt) 336 ∗ stackAt sp chainNewStackExt := by
  unfold stackAt
  have hbase : sp - BitVec.ofNat 64 chainNewStackExt =
      sp - BitVec.ofNat 64 chainFromStackExt + 336#64 := by
    change sp - 17840#64 = sp - 18176#64 + 336#64; bv_omega
  exact ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 chainFromStackExt)
    (n := 336) (k := chainNewStackExt) (b' := sp - BitVec.ofNat 64 chainNewStackExt)
    rfl hbase (by decide)

set_option maxHeartbeats 1600000 in
/-- Contract-backed (`*Ext`) verification of `spqr::chain_from` (`0x531ac`, 76 instructions) at
`chainFromStackExt` (`18176` B), assuming `ChainFromPbOkX img A ext` and
`ChainNewOkExt img hkdf A ext`. -/
theorem chainFrom_ok_of_contracts_ext {img : Obj.Image} {hkdf : HkdfFn}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hpb : ChainFromPbOkX img A ext)
    (hnew : ChainNewOkExt img hkdf A ext) :
    ChainFromOkExt img hkdf A ext := by
  unfold ChainFromOkExt tripleRatchetProgAtExt
  wpp_init x s0
  have hfn : libsignalSessionCode.fnOff chainFromName = 0x4ddb4 := chainFrom_fnOff
  code_fetches libsignalSessionCode libsignalSessionBin img.base
    (Rust.withPanics ext) hfn 0x4ddb4 304
  have h_from_pb := sub_ok_at_rebase (name := chainFromName) (callee := chainFromPbName)
    (k := num% (0x5ac7c - 0x4ddb4)) (by rw [chainFrom_fnOff, chainFromPb_fnOff]) hpb
  have h_new := sub_ok_at_rebase (name := chainFromName) (callee := chainNewName)
    (k := num% (0x5aaac - 0x4ddb4)) (by rw [chainFrom_fnOff, chainNew_fnOff]) hnew
  replace hpc : s0.pc =
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainFromName :=
    hpc.trans (by rw [Program.fnAddr_rebase, hfn])
  clear hpb hnew hfn
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainFromName = entry
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  rcases x with ⟨out, pbPtr, vnOptPtr, gPb, vnPin, pb, vn⟩
  have hinv0 : ImgCallInv img s0 := ⟨h_2, h_1⟩
  subst h_4 h_3 h
  refine SepWPp.rw_pre (by
    simp only [stackAt_chainFromExt_split_x s0.sp, stackAt_chainFrom_split s0.sp,
      sepExists_sepConj_left, sepExists_sepConj_right]
    rfl) ?_
  wp_elim_exists
  cases pb with
  | some chainPb =>
    have hcf_eq : chainFrom hkdf (some chainPb) vn = Chain.fromPb chainPb := rfl
    dsimp only [optChainPBAt]
    refine SepWPp.fold (chainPBAt_expose_cap A gPb (s0.readReg64 (.gpr 1#5)) chainPb)
      (by sep_focus) ?_
    refine SepWPp.pure_left_focus _ (by sep_focus) fun hcap_ne => ?_
    have hz_cap : (gPb.linksCap + 1#64 == 0#64) = false := add_one_beq_zero_of_ne_noneCap hcap_ne
    refine SepWPp.of_sepWP_inImage (mid := entry + bv% (0x5ac7c - 0x4ddb4)) hinv0 ?_
    wp_steps
    refine SepWP.fold (chainPBAt_unexpose_cap A gPb (s0.readReg64 (.gpr 1#5)) chainPb)
      (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    apply (SepWPp.call_frame_inImage_ret h_from_pb
      (⟨s0.sp - 120#64, s0.readReg64 (.gpr 1#5), gPb, chainPb⟩ : ChainFromPbCall)
      hinv1 (callee_ret_pc := entry + 44#64))
    · wp_focus_close wp_norm_goal
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · rfl
    · refine ⟨by wp_norm_lhs, by wp_norm_lhs⟩
    · rw [sp_of_imgCallInv hinv1 (sp' := s0.sp - 144#64) (by wp_norm_lhs)]
      sep_focus
    · intro sf
      exact onPanic_entails_of_trace_eq (by wp_norm_lhs)
    · intro _ _; rfl
    · intro sf hpc_sf hrun_sf hsp_sf hcs_sf
      dsimp only [chainFromPbSpecX]
      have hsp_sf' : sf.sp = s0.sp - 144#64 := hsp_sf.trans (by wp_norm_lhs)
      have hx19_sf : sf.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 0#5) :=
        hcs_sf.1.trans (by wp_norm_lhs)
      rw [sp_of_imgCallInv hinv1 (sp' := s0.sp - 144#64) (by wp_norm_lhs)]
      refine SepWP.focus_pure (by sep_focus) fun htr_sf => ?_
      rw [hcf_eq]
      cases hres : Chain.fromPb chainPb with
      | ok ch =>
        dsimp only [chainResultAt]
        refine SepWP.fold (chainRepr_entails_words11 A (s0.sp - 120#64) ch)
          (by sep_focus) ?_
        refine SepWP.rw_pre (by
          simp only [sepExists_sepConj_left, sepConj_assoc]
          rfl) ?_
        apply SepWP.exists_elim; intro G
        apply SepWP.exists_elim; intro pad
        refine SepWP.focus_pure (by sep_focus) fun hcap_ch_ne => ?_
        have hz_ch : (G.linksCap + 1#64 == 0#64) = false := add_one_beq_zero_of_ne_noneCap hcap_ch_ne
        refine SepWP.rw_pre (by
          simp only [memRegion_88_words11 (s0.readReg64 (.gpr 0#5)),
            sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
          rfl) ?_
        wp_elim_exists
        wp_steps
        refine SepWP.fold (words11_entails_chainRepr A (s0.readReg64 (.gpr 0#5)) G ch pad)
          (by sep_focus) ?_
        refine SepWP.fold (words11_to_memRegion_88 (s0.sp - 120#64)
          G.linksCap G.linksPtr G.linksHead (BitVec.ofNat 64 (G.epochs.zip ch.links).length)
          G.nextRoot.cap G.nextRoot.ptr (BitVec.ofNat 64 ch.nextRoot.length)
          ch.currentEpoch ch.sendEpoch (ch.params.maxOooKeys ++ ch.params.maxJump)
          (pad ++ ch.dir.toI32)) (by sep_focus) ?_
        refine SepWP.fold (stackAt_chainFrom_join s0.sp _ _ _ _ _ _) (by sep_focus) ?_
        refine SepWP.fold (Entails.of_eq (stackAt_chainFromExt_split_x s0.sp).symm) (by sep_focus) ?_
        wp_done
      | error err =>
        dsimp only [chainResultAt]
        refine SepWP.rw_pre (by
          simp only [chainErrorAt_unpack_words4 (s0.sp - 120#64) err,
            sepExists_sepConj_left, sepConj_assoc]
          rfl) ?_
        apply SepWP.exists_elim; intro q0_err
        apply SepWP.exists_elim; intro w3_err
        refine SepWP.rw_pre (by
          simp only [memRegion_88_words4_rest (s0.readReg64 (.gpr 0#5)),
            sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
          rfl) ?_
        wp_elim_exists
        refine SepWP.focus_pure (by sep_focus) fun htag_q0 => ?_
        refine SepWP.rw_pre (by simp only [noneCap]; rfl) ?_
        wp_steps
        refine SepWP.fold (chainErrorAt_pack_words4 (s0.readReg64 (.gpr 0#5)) err q0_err w3_err htag_q0)
          (by sep_focus) ?_
        refine SepWP.fold (words4_rest_to_memRegion_88 (s0.sp - 120#64)
          18446744073709551615#64 (q0_err.extractLsb' 0 64) (q0_err.extractLsb' 64 64) w3_err)
          (by sep_focus) ?_
        refine SepWP.fold (stackAt_chainFrom_join s0.sp _ _ _ _ _ _) (by sep_focus) ?_
        refine SepWP.fold (Entails.of_eq (stackAt_chainFromExt_split_x s0.sp).symm) (by sep_focus) ?_
        wp_done
  | none =>
    dsimp only [optChainPBAt, noneCap]
    cases vn with
    | none =>
      have hcf_eq : chainFrom hkdf none none = .error .chainNotAvailable := rfl
      dsimp only [optVersionNegotiationRefAt]
      refine SepWPp.pure_left_focus _ (by sep_focus) fun hvn0 => ?_
      refine SepWPp.rw_pre (by
        simp only [memRegion_88_err_split (s0.readReg64 (.gpr 0#5)),
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        rfl) ?_
      apply SepWPp.exists_elim; intro w2_out
      apply SepWPp.exists_elim; intro w1_out
      apply SepWPp.exists_elim; intro bs7_out
      apply SepWPp.exists_elim; intro b0_out
      apply SepWPp.exists_elim; intro w0_out
      refine SepWPp.pure_left_focus _ (by sep_focus) fun hbs7 => ?_
      apply SepWPp.of_sepWP_ret
      wp_steps
      rw [hcf_eq]
      dsimp only [chainResultAt]
      refine SepWP.fold (fold_chainErrorAt (s0.readReg64 (.gpr 0#5)) .chainNotAvailable 15#8 rfl hbs7 w1_out w2_out)
        (by sep_focus) ?_
      refine SepWP.fold (word_rest72_to_memRegion_80 (s0.readReg64 (.gpr 1#5)) 18446744073709551615#64)
        (by sep_focus) ?_
      refine SepWP.fold (stackAt_chainFrom_join s0.sp _ _ _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (Entails.of_eq (stackAt_chainFromExt_split_x s0.sp).symm) (by sep_focus) ?_
      wp_done
    | some v =>
      dsimp only [optVersionNegotiationRefAt, versionNegotiationPBAt]
      refine SepWPp.pure_left_focus _ (by sep_focus) fun hvn_ne => ?_
      rcases direction_fromI32_or v.direction with
        ⟨dir, hdir_val, hdir_opt, hcond_hi⟩ | ⟨hdir_opt, hcond_hi⟩
      · cases hcp : v.chainParams with
        | none =>
          have hcf_eq : chainFrom hkdf none (some v) = .error .chainNotAvailable := by
            simp [chainFrom, chainFromVersionNegotiation, hdir_opt, hcp]; rfl
          dsimp only [optChainParamsPBAt]
          refine SepWPp.rw_pre (by
            simp only [memRegion_88_err_split (s0.readReg64 (.gpr 0#5)),
              sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
            rfl) ?_
          apply SepWPp.exists_elim; intro w2_out
          apply SepWPp.exists_elim; intro w1_out
          apply SepWPp.exists_elim; intro bs7_out
          apply SepWPp.exists_elim; intro b0_out
          apply SepWPp.exists_elim; intro w0_out
          refine SepWPp.pure_left_focus _ (by sep_focus) fun hbs7 => ?_
          apply SepWPp.of_sepWP_ret
          wp_steps
          rw [hcf_eq]
          dsimp only [chainResultAt]
          refine SepWP.fold (fold_chainErrorAt (s0.readReg64 (.gpr 0#5)) .chainNotAvailable 15#8 rfl hbs7 w1_out w2_out)
            (by sep_focus) ?_
          refine SepWP.fold (word_rest72_to_memRegion_80 (s0.readReg64 (.gpr 1#5)) 18446744073709551615#64)
            (by sep_focus) ?_
          refine SepWP.fold (stackAt_chainFrom_join s0.sp _ _ _ _ _ _) (by sep_focus) ?_
          refine SepWP.fold (Entails.of_eq (stackAt_chainFromExt_split_x s0.sp).symm) (by sep_focus) ?_
          wp_done
        | some cp =>
          have hcf_eq : chainFrom hkdf none (some v) =
              .ok (chainNewVal hkdf v.authKey dir cp) := by
            simp [chainFrom, chainFromVersionNegotiation, hdir_opt, hcp]; rfl
          dsimp only [optChainParamsPBAt]
          refine SepWPp.fold (vecU8At_entails_header_bytesAt_rest A
            (s0.readReg64 (.gpr 2#5)) vnPin.cap vnPin.ptr v.authKey) (by sep_focus) ?_
          refine SepWPp.pure_left_focus _ (by sep_focus) fun hlen64 => ?_
          refine SepWPp.of_sepWP_inImage (mid := entry + bv% (0x5aaac - 0x4ddb4)) hinv0 ?_
          wp_steps
          refine SepWP.fold (word_rest72_to_memRegion_80 (s0.readReg64 (.gpr 1#5)) 18446744073709551615#64)
            (by sep_focus) ?_
          refine SepWP.fold (stackAt_chainFrom_join s0.sp _ _ _ _ _ _) (by sep_focus) ?_
          refine SepWP.fold (Entails.of_eq (stackAt_chainFromExt_split_x s0.sp).symm) (by sep_focus) ?_
          refine SepWP.rw_pre (by
            simp only [stackAt_chainFromExt_split_chainNewExt s0.sp, sepConj_assoc]
            rfl) ?_
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          intro hinv1
          apply (SepWPp.tail_call_frame_inImage h_new
            (⟨s0.readReg64 (.gpr 0#5), false, vnPin.ptr, v.authKey, dir, cp⟩ : ChainNewGhost)
            hinv1)
          · wp_focus_close wp_norm_goal
          · wp_focus_close wp_norm_lhs
          · wp_focus_close wp_norm_lhs
          · wp_focus_close wp_norm_lhs
          · rfl
          · refine ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hlen64, Or.inl Bool.noConfusion⟩
          · rw [sp_of_imgCallInv hinv1 (sp' := s0.sp) (by wp_norm_lhs)]
            sep_focus
          · intro sf
            exact onPanic_entails_of_trace_eq (by wp_norm_lhs)
          · intro _ _; rfl
          · intro sf hpc_sf hrun_sf hsp_sf hcs_sf
            dsimp only [chainNewSpecExt]
            rw [sp_of_imgCallInv hinv1 (sp' := s0.sp) (by wp_norm_lhs)]
            refine SepWP.focus_pure (by sep_focus) fun htr_sf => ?_
            rw [hcf_eq]
            dsimp only [chainResultAt]
            refine SepWP.fold (chainNew_post_entails_chainRepr A (s0.readReg64 (.gpr 0#5)) _)
              (by sep_focus) ?_
            refine SepWP.fold (header_bytesAt_rest_entails_vecU8At A
              (s0.readReg64 (.gpr 2#5)) vnPin.cap vnPin.ptr v.authKey) (by sep_focus) ?_
            refine SepWP.fold (Entails.of_eq (stackAt_chainFromExt_split_chainNewExt s0.sp).symm)
              (by sep_focus) ?_
            wp_done
      · have hcf_eq : chainFrom hkdf none (some v) = .error .stateDecode := by
          simp [chainFrom, chainFromVersionNegotiation, hdir_opt]; rfl
        refine SepWPp.rw_pre (by
          simp only [memRegion_88_err_split (s0.readReg64 (.gpr 0#5)),
            sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
          rfl) ?_
        apply SepWPp.exists_elim; intro w2_out
        apply SepWPp.exists_elim; intro w1_out
        apply SepWPp.exists_elim; intro bs7_out
        apply SepWPp.exists_elim; intro b0_out
        apply SepWPp.exists_elim; intro w0_out
        refine SepWPp.pure_left_focus _ (by sep_focus) fun hbs7 => ?_
        apply SepWPp.of_sepWP_ret
        wp_steps
        rw [hcf_eq]
        dsimp only [chainResultAt]
        refine SepWP.fold (fold_chainErrorAt (s0.readReg64 (.gpr 0#5)) .stateDecode 0#8 rfl hbs7 w1_out w2_out)
          (by sep_focus) ?_
        refine SepWP.fold (word_rest72_to_memRegion_80 (s0.readReg64 (.gpr 1#5)) 18446744073709551615#64)
          (by sep_focus) ?_
        refine SepWP.fold (stackAt_chainFrom_join s0.sp _ _ _ _ _ _) (by sep_focus) ?_
        refine SepWP.fold (Entails.of_eq (stackAt_chainFromExt_split_x s0.sp).symm) (by sep_focus) ?_
        wp_done

abbrev chainFrom_ok_ext := @chainFrom_ok_of_contracts_ext

end CryptoVerification.SpqrV1.Top.ChainFrom
