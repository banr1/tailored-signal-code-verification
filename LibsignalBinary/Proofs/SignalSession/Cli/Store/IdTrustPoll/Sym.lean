/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPoll.Callees
import all Init.Data.String.Defs
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.RecordCodecs.RoundTrip
import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPoll.Fetches
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
public import LibsignalBinary.Specifications.AsmConstants -- shake: keep
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.Store.IdTrustPoll.Helpers

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoGames.LibsignalSessionApi CryptoVerification.RecordCodecs
open CryptoVerification.LibsignalSession CryptoVerification.CodeLayout
open CryptoVerification.SignalSession.Cli

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace CliIdTrustPollNorm

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_writeVReg128_pre (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem fs_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).fs = s.fs := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem fs_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).fs = s.fs := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem fs_setPState_pre (s : State) (ps : PState) :
    (s.setPState ps).fs = s.fs := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem fs_writeReg64_pre (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).fs = s.fs := by cases s; cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem fs_writeReg32_pre (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).fs = s.fs := by cases s; cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem fs_writeReg_pre (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).fs = s.fs := by cases s; cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem fs_writeVReg128_pre (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).fs = s.fs := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem trace_writeVReg128_pre (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).trace = s.trace := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_writeVReg128_pre (s : State) (idx : BitVec 5) (v : BitVec 128) (r : Reg) :
    (s.writeVReg128 idx v).readReg64 r = s.readReg64 r := by
  cases s; cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_writeVReg128_pre (s : State) (idx : BitVec 5) (v : BitVec 128) (r : Reg) :
    (s.writeVReg128 idx v).readReg32 r = s.readReg32 r := by
  cases s; cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_writeVReg128_pre (s : State) (idx : BitVec 5) (v : BitVec 128)
    (w : RegWidth) (r : Reg) :
    (s.writeVReg128 idx v).readReg w r = s.readReg w r := by
  cases s; cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readVReg128_setPC_pre (s : State) (pc : BitVec 64) (idx : BitVec 5) :
    (s.setPC pc).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readVReg128_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (idx : BitVec 5) :
    ((s.setPC pc).setMem m).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readVReg128_setMem_pre (s : State) (m : Memory) (idx : BitVec 5) :
    (s.setMem m).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readVReg128_setPState_pre (s : State) (ps : PState) (idx : BitVec 5) :
    (s.setPState ps).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readVReg128_writeReg64_pre (s : State) (r : Reg) (v : BitVec 64) (idx : BitVec 5) :
    (s.writeReg64 r v).readVReg128 idx = s.readVReg128 idx := by
  cases s; cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readVReg128_writeReg32_pre (s : State) (r : Reg) (v : BitVec 32) (idx : BitVec 5) :
    (s.writeReg32 r v).readVReg128 idx = s.readVReg128 idx := by
  cases s; cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readVReg128_writeReg_pre (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64)
    (idx : BitVec 5) :
    (s.writeReg w r v).readVReg128 idx = s.readVReg128 idx := by
  cases s; cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem extractLsb_append_lo (hi lo : BitVec 64) :
    BitVec.extractLsb' 0 64 (hi ++ lo) = lo := by
  bv_bits

@[local arm64_norm ↓, local wp_norm ↓]
theorem extractLsb_append_hi (hi lo : BitVec 64) :
    BitVec.extractLsb' 64 64 (hi ++ lo) = hi := by
  bv_bits

@[local arm64_norm ↓, local wp_norm ↓]
theorem extractLsb_pack32_0 (a b c d : BitVec 8) :
    BitVec.extractLsb' 0 8 (a ++ b ++ c ++ d) = d := by
  bv_bits

@[local arm64_norm ↓, local wp_norm ↓]
theorem extractLsb_pack32_8 (a b c d : BitVec 8) :
    BitVec.extractLsb' 8 8 (a ++ b ++ c ++ d) = c := by
  bv_bits

@[local arm64_norm ↓, local wp_norm ↓]
theorem extractLsb_pack32_16 (a b c d : BitVec 8) :
    BitVec.extractLsb' 16 8 (a ++ b ++ c ++ d) = b := by
  bv_bits

@[local arm64_norm ↓, local wp_norm ↓]
theorem extractLsb_pack32_24 (a b c d : BitVec 8) :
    BitVec.extractLsb' 24 8 (a ++ b ++ c ++ d) = a := by
  bv_bits

@[local arm64_norm ↓, local wp_norm ↓]
theorem extractLsb_pack32_0_16 (a b c d : BitVec 8) :
    BitVec.extractLsb' 0 16 (a ++ b ++ c ++ d) = c ++ d := by
  bv_bits

@[local arm64_norm ↓, local wp_norm ↓]
theorem extractLsb_pack32_16_16 (a b c d : BitVec 8) :
    BitVec.extractLsb' 16 16 (a ++ b ++ c ++ d) = a ++ b := by
  bv_bits

@[local arm64_norm ↓, local wp_norm ↓]
theorem speWord_one_eq : speWord 1 = asm64% speNicheBase + 1#64 := rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem okTagVec_eq_neg2 : okTagVec = -2#64 := rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem trace_writeReg32_pre (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).trace = s.trace := by cases s; cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem trace_writeReg_pre (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).trace = s.trace := by cases s; cases w <;> cases r <;> rfl

end CliIdTrustPollNorm

open CliIdTrustPollNorm

private theorem utf8_read_len_eq : BitVec.ofNat 64 (utf8 "read").length = 4#64 := by
  decide +kernel

private theorem close_panic_subgoal {s0 s_call sf : State} {F R : SepProp}
    (htr : s_call.trace = s0.trace)
    (hm : sf.mem ⊨ ((⌜allocFailedIn s_call sf ∧ s_call.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R := by
  refine allowPanic_frame ?_ (by rwa [sepConj_assoc] at hm)
  rintro ⟨hfail, hpref⟩
  unfold allocFailedIn at hfail ⊢
  rw [htr] at hfail hpref
  exact ⟨hfail, hpref⟩

private def idTrustPostAns (A : RustAlloc) (out : BitVec 64)
    (dget : Except Unit (List (BitVec 8))) (key : IdentityKey)
    (s0 sf : State) : SepProp :=
  ∃∗ gr : Except Unit (List (BitVec 8)),
  ∃∗ p : Except Unit (Option IdentityKey),
    ⌜(gr = dget ∧ sf.trace = s0.trace) ∧ IdPeerAns gr p⌝ ∗
    idTrustOutAt A out (idTrustOf p key)

private theorem idTrustPostAns_intro (A : RustAlloc) (out : BitVec 64)
    (dget gr : Except Unit (List (BitVec 8))) (p : Except Unit (Option IdentityKey))
    (key : IdentityKey) (s0 sf : State)
    (hpure : (gr = dget ∧ sf.trace = s0.trace) ∧ IdPeerAns gr p) :
    idTrustOutAt A out (idTrustOf p key) ⊢
      idTrustPostAns A out dget key s0 sf := by
  have htrue : (((gr = dget ∧ sf.trace = s0.trace) ∧ IdPeerAns gr p) : Prop) = True :=
    propext ⟨fun _ => trivial, fun _ => hpure⟩
  unfold idTrustPostAns
  refine Entails.sepExists_right gr (Entails.sepExists_right p ?_)
  rw [htrue]
  exact Entails.of_eq (by simp)

private theorem focus_postAns (A : RustAlloc) (out : BitVec 64)
    (dget gr : Except Unit (List (BitVec 8))) (p : Except Unit (Option IdentityKey))
    (key : IdentityKey) (s0 : State)
    {prog : Program} {ret_pc : BitVec 64} {s_ret : State}
    {P R : SepProp} {post : State → SepProp → Prop}
    (hf : P = idTrustOutAt A out (idTrustOf p key) ∗ R)
    (hpure : (gr = dget ∧ s_ret.trace = s0.trace) ∧ IdPeerAns gr p)
    (hnext : SepWP prog ret_pc s_ret (idTrustPostAns A out dget key s0 s_ret ∗ R) post) :
    SepWP prog ret_pc s_ret P post :=
  SepWP.focus_weaken (idTrustPostAns_intro A out dget gr p key s0 s_ret hpure) (hf := hf) hnext

private theorem focus_out_err_fold (A : RustAlloc) (out : BitVec 64)
    (sCap sPtr : BitVec 64) (sBs : List (BitVec 8)) (fnPtr : BitVec 64)
    {prog : Program} {ret_pc : BitVec 64} {s_ret : State}
    {P R : SepProp} {post : State → SepProp → Prop}
    {b8 : BitVec 8} {w9 : BitVec 32} {h13 : BitVec 16} {b15 : BitVec 8}
    {b40 b41 b42 b43 : BitVec 8} {w44 : BitVec 32}
    (hf : P = ((out ↦₆₄ speWord 1) ∗
        (((out + 8#64) ↦₈ b8) ∗ ((out + 9#64) ↦₃₂ w9) ∗
          ((out + 13#64) ↦₁₆ h13) ∗ ((out + 15#64) ↦₈ b15)) ∗
        ((out + 16#64) ↦₆₄ sPtr) ∗ ((out + 24#64) ↦₆₄ BitVec.ofNat 64 sBs.length) ∗
        SpqrV1.Alloc.vecU8Buf A sCap sPtr sBs ∗
        ((out + 32#64) ↦₆₄ fnPtr) ∗
        (((out + 40#64) ↦₈ b40) ∗ ((out + 41#64) ↦₈ b41) ∗
          ((out + 42#64) ↦₈ b42) ∗ ((out + 43#64) ↦₈ b43) ∗ ((out + 44#64) ↦₃₂ w44)) ∗
        (fnPtr ↦ᵣ utf8 "read")) ∗ R)
    (hsCap : b15 ++ h13 ++ w9 ++ b8 = sCap)
    (hfnLen : w44 ++ b43 ++ b42 ++ b41 ++ b40 = 4#64)
    (hnext : SepWP prog ret_pc s_ret (idTrustOutAt A out (.error ()) ∗ R) post) :
    SepWP prog ret_pc s_ret P post :=
  SepWP.focus_weaken
    (out_err_fold A out sCap sPtr sBs fnPtr b8 w9 h13 b15 b40 b41 b42 b43 w44
      hsCap (hfnLen.trans utf8_read_len_eq.symm))
    (hf := hf) hnext

private theorem focus_pollKeyChunks_sp_144 (sp : BitVec 64) {bs : List (BitVec 8)}
    {kw0 : BitVec 32} {kw4 : BitVec 16} {kb6 : BitVec 8}
    {kv7 kv15 kv23 : BitVec 64} {kb31 : BitVec 8}
    (hchunks : ∀ a : BitVec 64, (a ↦ₛ bs) = pollKeyChunks a kw0 kw4 kb6 kv7 kv15 kv23 kb31)
    {prog : Program} {target : BitVec 64} {s : State}
    {P R : SepProp} {post : State → SepProp → Prop}
    {w0' : BitVec 32} {w4' : BitVec 16} {b6' : BitVec 8}
    (hf : P = (((sp - 144#64) ↦₃₂ w0') ∗ ((sp - 140#64) ↦₁₆ w4') ∗
        ((sp - 138#64) ↦₈ b6') ∗ ((sp - 137#64) ↦₆₄ kv7) ∗
        ((sp - 129#64) ↦₆₄ kv15) ∗ ((sp - 121#64) ↦₆₄ kv23) ∗
        ((sp - 113#64) ↦₈ kb31)) ∗ R)
    (hw0 : w0' = kw0) (hw4 : w4' = kw4) (hb6 : b6' = kb6)
    (hnext : SepWP prog target s (((sp - 144#64) ↦ₛ bs) ∗ R) post) :
    SepWP prog target s P post := by
  rw [hf, pollKeyChunks_sp_144_of_eq sp hchunks hw0 hw4 hb6]
  exact hnext

private theorem unpack_getResultAt_err {prog : Program} {ret : BitVec 64} {sf : State}
    {A : RustAlloc} {sp : BitVec 64} {rest : SepProp}
    {Q Qp : State → SepProp → Prop}
    (h : ∀ (fnPtr : BitVec 64) (sBs : List (BitVec 8)) (sCap sPtr : BitVec 64),
      SepWPp prog ret sf
        (((sp - 144#64) ↦₆₄ speWord 1) ∗
          ((sp - 136#64) ↦₆₄ sCap) ∗ ((sp - 128#64) ↦₆₄ sPtr) ∗
          ((sp - 120#64) ↦₆₄ BitVec.ofNat 64 sBs.length) ∗
          SpqrV1.Alloc.vecU8Buf A sCap sPtr sBs ∗
          ((sp - 112#64) ↦₆₄ fnPtr) ∗
          ((sp - 104#64) ↦₆₄ 4#64) ∗
          (fnPtr ↦ᵣ utf8 "read") ∗ rest) Q Qp) :
    SepWPp prog ret sf (getResultAt A (sp - 144#64) (.error ()) ∗ rest) Q Qp := by
  rw [getResultAt_err_sp_144 A sp, utf8_read_len_eq]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply ProofLib.SepWPp.exists_elim; intro fnPtr
  apply ProofLib.SepWPp.exists_elim; intro sBs
  apply ProofLib.SepWPp.exists_elim; intro sCap
  apply ProofLib.SepWPp.exists_elim; intro sPtr
  exact h fnPtr sBs sCap sPtr

private theorem unpack_getResultAt_ok {prog : Program} {ret : BitVec 64} {sf : State}
    {A : RustAlloc} {sp : BitVec 64} {bs : List (BitVec 8)} {rest : SepProp}
    {Q Qp : State → SepProp → Prop}
    (h : ∀ (bCap bPtr : BitVec 64),
      bs.length ≤ bCap.toNat → bCap.toNat < 2 ^ 63 → bPtr ≠ 0#64 →
      SepWPp prog ret sf
        (((sp - 144#64) ↦₆₄ okTagVec) ∗ ((sp - 136#64) ↦₆₄ bCap) ∗
          ((sp - 128#64) ↦₆₄ bPtr) ∗ ((sp - 120#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (bPtr ↦ₛ bs) ∗ vecU8BufRest A bCap bPtr bs.length ∗
          memRegion (sp - 112#64) 16 ∗ rest) Q Qp) :
    SepWPp prog ret sf (getResultAt A (sp - 144#64) (.ok bs) ∗ rest) Q Qp := by
  rw [getResultAt_ok_sp_144 A sp bs]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply ProofLib.SepWPp.exists_elim; intro bCap
  apply ProofLib.SepWPp.exists_elim; intro bPtr
  apply ProofLib.SepWPp.pure_elim; rintro ⟨h1, h2, h3⟩
  exact h bCap bPtr h1 h2 h3

private theorem cells_24_lo (sp : BitVec 64) :
    cells (sp - 192#64) 24 =
      (∃∗ v0 : BitVec 64, (sp - 192#64) ↦₆₄ v0) ∗
      ((∃∗ b1 : BitVec 8, (sp - 184#64) ↦₈ b1) ∗ memRegion (sp - 183#64) 7) ∗
      (∃∗ v2 : BitVec 64, (sp - 176#64) ↦₆₄ v2) ∗
      ((∃∗ b3 : BitVec 8, (sp - 168#64) ↦₈ b3) ∗ memRegion (sp - 167#64) 7) ∗
      (∃∗ v4 : BitVec 64, (sp - 160#64) ↦₆₄ v4) ∗
      ((∃∗ b5 : BitVec 8, (sp - 152#64) ↦₈ b5) ∗ memRegion (sp - 151#64) 7) ∗
      memRegion (sp - 144#64) 48 ∗
      (∃∗ s29 : BitVec 64, (sp - 96#64) ↦₆₄ s29) ∗
      (∃∗ s30 : BitVec 64, (sp - 88#64) ↦₆₄ s30) ∗
      (∃∗ s27 : BitVec 64, (sp - 80#64) ↦₆₄ s27) ∗
      ((∃∗ w0 : BitVec 32, (sp - 72#64) ↦₃₂ w0) ∗
        (∃∗ b4 : BitVec 8, (sp - 68#64) ↦₈ b4) ∗
        (∃∗ b5 : BitVec 8, (sp - 67#64) ↦₈ b5) ∗
        (∃∗ b6 : BitVec 8, (sp - 66#64) ↦₈ b6) ∗
        (∃∗ b7 : BitVec 8, (sp - 65#64) ↦₈ b7)) ∗
      (∃∗ s26 : BitVec 64, (sp - 64#64) ↦₆₄ s26) ∗
      (∃∗ s25 : BitVec 64, (sp - 56#64) ↦₆₄ s25) ∗
      (∃∗ s24 : BitVec 64, (sp - 48#64) ↦₆₄ s24) ∗
      (∃∗ s23 : BitVec 64, (sp - 40#64) ↦₆₄ s23) ∗
      (∃∗ s22 : BitVec 64, (sp - 32#64) ↦₆₄ s22) ∗
      (∃∗ s21 : BitVec 64, (sp - 24#64) ↦₆₄ s21) ∗
      (∃∗ s20 : BitVec 64, (sp - 16#64) ↦₆₄ s20) ∗
      (∃∗ s19 : BitVec 64, (sp - 8#64) ↦₆₄ s19) := by
  rw [cells_24_split sp, memRegion_8_sp_72_lo sp]

private theorem cells_24_hi (sp : BitVec 64) :
    cells (sp - 192#64) 24 =
      (∃∗ v0 : BitVec 64, (sp - 192#64) ↦₆₄ v0) ∗
      ((∃∗ b1 : BitVec 8, (sp - 184#64) ↦₈ b1) ∗ memRegion (sp - 183#64) 7) ∗
      (∃∗ v2 : BitVec 64, (sp - 176#64) ↦₆₄ v2) ∗
      ((∃∗ b3 : BitVec 8, (sp - 168#64) ↦₈ b3) ∗ memRegion (sp - 167#64) 7) ∗
      (∃∗ v4 : BitVec 64, (sp - 160#64) ↦₆₄ v4) ∗
      ((∃∗ b5 : BitVec 8, (sp - 152#64) ↦₈ b5) ∗ memRegion (sp - 151#64) 7) ∗
      memRegion (sp - 144#64) 48 ∗
      (∃∗ s29 : BitVec 64, (sp - 96#64) ↦₆₄ s29) ∗
      (∃∗ s30 : BitVec 64, (sp - 88#64) ↦₆₄ s30) ∗
      (∃∗ s27 : BitVec 64, (sp - 80#64) ↦₆₄ s27) ∗
      ((∃∗ b0 : BitVec 8, (sp - 72#64) ↦₈ b0) ∗
        (∃∗ b1 : BitVec 8, (sp - 71#64) ↦₈ b1) ∗
        (∃∗ b2 : BitVec 8, (sp - 70#64) ↦₈ b2) ∗
        (∃∗ w3 : BitVec 32, (sp - 69#64) ↦₃₂ w3) ∗
        (∃∗ b7 : BitVec 8, (sp - 65#64) ↦₈ b7)) ∗
      (∃∗ s26 : BitVec 64, (sp - 64#64) ↦₆₄ s26) ∗
      (∃∗ s25 : BitVec 64, (sp - 56#64) ↦₆₄ s25) ∗
      (∃∗ s24 : BitVec 64, (sp - 48#64) ↦₆₄ s24) ∗
      (∃∗ s23 : BitVec 64, (sp - 40#64) ↦₆₄ s23) ∗
      (∃∗ s22 : BitVec 64, (sp - 32#64) ↦₆₄ s22) ∗
      (∃∗ s21 : BitVec 64, (sp - 24#64) ↦₆₄ s21) ∗
      (∃∗ s20 : BitVec 64, (sp - 16#64) ↦₆₄ s20) ∗
      (∃∗ s19 : BitVec 64, (sp - 8#64) ↦₆₄ s19) := by
  rw [cells_24_split sp, memRegion_8_sp_72_hi sp]

private def cliIdTrustPollExpandedSpec (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustAlloc) (img : Obj.Image) (calleeStk : Nat) : Spec IdPollGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.call.fut ∧ s.readReg64 .x8 = x.call.out ∧
      x.call.call.addr.name.bytes.length < 2 ^ 32 ∧ x.peers.path.length < 2 ^ 32 ∧
      pathOk (pathOf x.peers.path x.call.call.addr.name.bytes) ∧
      (∀ bs, x.peers.get rd s.fs.files x.call.call.addr.name.bytes = .ok bs → IdFileWf bs) ∧
      x.call.call.addr.name.bytes.length ≤ x.call.call.addr.name.cap.toNat ∧
      x.call.call.addr.name.cap.toNat < 2 ^ 63 ∧ x.call.call.addr.name.ptr ≠ 0#64⌝ ∗
      (x.call.fut ↦₆₄ x.self) ∗ ((x.call.fut + 8#64) ↦₆₄ x.call.call.addrA) ∗
      ((x.call.fut + 16#64) ↦₆₄ x.call.call.keyA) ∗ ((x.call.fut + 24#64) ↦₈ 0#8) ∗
      dirAt A (x.self + 40#64) x.peers ∗
      memRegion x.call.out 48 ∗
      (x.call.call.addrA ↦₆₄ x.call.call.addr.name.cap) ∗
      ((x.call.call.addrA + 8#64) ↦₆₄ x.call.call.addr.name.ptr) ∗
      ((x.call.call.addrA + 16#64) ↦₆₄ BitVec.ofNat 64 x.call.call.addr.name.bytes.length) ∗
      (x.call.call.addr.name.ptr ↦ₛ x.call.call.addr.name.bytes) ∗
      (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗ logOff img ∗
      A.pool ∗ stackAt (s.sp - 192#64) calleeStk ∗
      ((∃∗ v0 : BitVec 64, (s.sp - 192#64) ↦₆₄ v0) ∗
        ((∃∗ b1 : BitVec 8, (s.sp - 184#64) ↦₈ b1) ∗ memRegion (s.sp - 183#64) 7) ∗
        (∃∗ v2 : BitVec 64, (s.sp - 176#64) ↦₆₄ v2) ∗
        ((∃∗ b3 : BitVec 8, (s.sp - 168#64) ↦₈ b3) ∗ memRegion (s.sp - 167#64) 7) ∗
        (∃∗ v4 : BitVec 64, (s.sp - 160#64) ↦₆₄ v4) ∗
        ((∃∗ b5 : BitVec 8, (s.sp - 152#64) ↦₈ b5) ∗ memRegion (s.sp - 151#64) 7) ∗
        memRegion (s.sp - 144#64) 48 ∗
        (∃∗ s29 : BitVec 64, (s.sp - 96#64) ↦₆₄ s29) ∗
        (∃∗ s30 : BitVec 64, (s.sp - 88#64) ↦₆₄ s30) ∗
        (∃∗ s27 : BitVec 64, (s.sp - 80#64) ↦₆₄ s27) ∗
        ((∃∗ w0 : BitVec 32, (s.sp - 72#64) ↦₃₂ w0) ∗
          (∃∗ b4 : BitVec 8, (s.sp - 68#64) ↦₈ b4) ∗
          (∃∗ b5 : BitVec 8, (s.sp - 67#64) ↦₈ b5) ∗
          (∃∗ b6 : BitVec 8, (s.sp - 66#64) ↦₈ b6) ∗
          (∃∗ b7 : BitVec 8, (s.sp - 65#64) ↦₈ b7)) ∗
        (∃∗ s26 : BitVec 64, (s.sp - 64#64) ↦₆₄ s26) ∗
        (∃∗ s25 : BitVec 64, (s.sp - 56#64) ↦₆₄ s25) ∗
        (∃∗ s24 : BitVec 64, (s.sp - 48#64) ↦₆₄ s24) ∗
        (∃∗ s23 : BitVec 64, (s.sp - 40#64) ↦₆₄ s23) ∗
        (∃∗ s22 : BitVec 64, (s.sp - 32#64) ↦₆₄ s22) ∗
        (∃∗ s21 : BitVec 64, (s.sp - 24#64) ↦₆₄ s21) ∗
        (∃∗ s20 : BitVec 64, (s.sp - 16#64) ↦₆₄ s20) ∗
        (∃∗ s19 : BitVec 64, (s.sp - 8#64) ↦₆₄ s19))
  post := fun x s0 sf =>
    idTrustPostAns A x.call.out
      (x.peers.get rd s0.fs.files x.call.call.addr.name.bytes) x.call.call.key s0 sf ∗
      (x.call.fut ↦₆₄ x.self) ∗ ((x.call.fut + 8#64) ↦₆₄ x.call.call.addrA) ∗
      ((x.call.fut + 16#64) ↦₆₄ x.call.call.keyA) ∗ ((x.call.fut + 24#64) ↦₈ 1#8) ∗
      dirAt A (x.self + 40#64) x.peers ∗
      (x.call.call.addrA ↦₆₄ x.call.call.addr.name.cap) ∗
      ((x.call.call.addrA + 8#64) ↦₆₄ x.call.call.addr.name.ptr) ∗
      ((x.call.call.addrA + 16#64) ↦₆₄ BitVec.ofNat 64 x.call.call.addr.name.bytes.length) ∗
      (x.call.call.addr.name.ptr ↦ₛ x.call.call.addr.name.bytes) ∗
      (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗ logOff img ∗
      A.pool ∗ stackAt (s0.sp - 192#64) calleeStk ∗
      ((∃∗ v0 : BitVec 64, (s0.sp - 192#64) ↦₆₄ v0) ∗
        ((∃∗ b1 : BitVec 8, (s0.sp - 184#64) ↦₈ b1) ∗ memRegion (s0.sp - 183#64) 7) ∗
        (∃∗ v2 : BitVec 64, (s0.sp - 176#64) ↦₆₄ v2) ∗
        ((∃∗ b3 : BitVec 8, (s0.sp - 168#64) ↦₈ b3) ∗ memRegion (s0.sp - 167#64) 7) ∗
        (∃∗ v4 : BitVec 64, (s0.sp - 160#64) ↦₆₄ v4) ∗
        ((∃∗ b5 : BitVec 8, (s0.sp - 152#64) ↦₈ b5) ∗ memRegion (s0.sp - 151#64) 7) ∗
        memRegion (s0.sp - 144#64) 48 ∗
        (∃∗ s29 : BitVec 64, (s0.sp - 96#64) ↦₆₄ s29) ∗
        (∃∗ s30 : BitVec 64, (s0.sp - 88#64) ↦₆₄ s30) ∗
        (∃∗ s27 : BitVec 64, (s0.sp - 80#64) ↦₆₄ s27) ∗
        ((∃∗ b0 : BitVec 8, (s0.sp - 72#64) ↦₈ b0) ∗
          (∃∗ b1 : BitVec 8, (s0.sp - 71#64) ↦₈ b1) ∗
          (∃∗ b2 : BitVec 8, (s0.sp - 70#64) ↦₈ b2) ∗
          (∃∗ w3 : BitVec 32, (s0.sp - 69#64) ↦₃₂ w3) ∗
          (∃∗ b7 : BitVec 8, (s0.sp - 65#64) ↦₈ b7)) ∗
        (∃∗ s26 : BitVec 64, (s0.sp - 64#64) ↦₆₄ s26) ∗
        (∃∗ s25 : BitVec 64, (s0.sp - 56#64) ↦₆₄ s25) ∗
        (∃∗ s24 : BitVec 64, (s0.sp - 48#64) ↦₆₄ s24) ∗
        (∃∗ s23 : BitVec 64, (s0.sp - 40#64) ↦₆₄ s23) ∗
        (∃∗ s22 : BitVec 64, (s0.sp - 32#64) ↦₆₄ s22) ∗
        (∃∗ s21 : BitVec 64, (s0.sp - 24#64) ↦₆₄ s21) ∗
        (∃∗ s20 : BitVec 64, (s0.sp - 16#64) ↦₆₄ s20) ∗
        (∃∗ s19 : BitVec 64, (s0.sp - 8#64) ↦₆₄ s19))
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

private theorem cliIdTrustPollExpandedSpec_eq (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustAlloc) (img : Obj.Image) (calleeStk : Nat) :
    cliIdTrustPollExpandedSpec rd pathOk A img calleeStk =
      cliIdTrustPollInnerSpec rd pathOk A img calleeStk := by
  unfold cliIdTrustPollExpandedSpec cliIdTrustPollInnerSpec idTrustPostAns
  congr 1
  · funext x s
    rw [cells_24_lo s.sp]
  · funext x s0 sf
    rw [cells_24_hi s0.sp]

set_option pp.deepTerms false in
set_option pp.maxSteps 1000000 in
set_option maxHeartbeats 3200000 in
private theorem idTrustPollInner_ok_of_cells {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {calleeStk : Nat}
    (hGetCells : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr idTrustPollName +
        bv% (ls_rel%
          "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}"
          "<libsignal_cli::stores::Dir>::get"))
      ((dirGetCellsSpec rd pathOk A calleeStk).inImage img))
    (hDecCells : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr idTrustPollName -
        bv% (ls_rel%
          "<libsignal_protocol::identity_key::IdentityKey>::decode"
          "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}"))
      ((ikDecodeCellsSpec img calleeStk).inImage img))
    (hDeallocCells : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr idTrustPollName +
        bv% (ls_rel%
          "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}"
          "__rustc::__rust_dealloc"))
      ((deallocVecBufSpec A calleeStk).inImage img))
    (hEqCells : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr idTrustPollName -
        bv% (ls_rel%
          "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq"
          "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}"))
      ((pkEqCellsSpec calleeStk).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr idTrustPollName)
      ((cliIdTrustPollInnerSpec rd pathOk A img calleeStk).inImage img) := by
  rw [← cliIdTrustPollExpandedSpec_eq]
  unfold Spec.inImage
  simp (config := { maxSteps := 2000000 }) only [cliIdTrustPollExpandedSpec,
    sepExists_sepConj_left, sepExists_sepConj_right]
  have hfn : libsignalSessionCode.fnOff idTrustPollName =
      num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}") :=
    idTrustPoll_fnOff
  code_fetches CryptoVerification.libsignalSessionCode cliIdTrustPollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}")) 500
  dsimp only [tripleRatchetProgAtExt] at hGetCells hDecCells hDeallocCells hEqCells ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr idTrustPollName = fnBase
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  have hinv0 : ImgCallInv img s0 := ⟨by assumption, by assumption⟩
  -- Prologue (`+0x0 .. +0x40`) -> `Dir::get`
  apply SepWPp.of_sepWP_inImage
    (mid := fnBase + bv% (ls_rel%
      "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}"
      "<libsignal_cli::stores::Dir>::get"))
    hinv0
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hinv1
  wp_call_inImage hGetCells hinv1
    (s0.sp - 144#64, x.self + 40#64, x.peers,
      x.call.call.addr.name.ptr, x.call.call.addr.name.bytes, s0.sp - 192#64)
  case panic =>
    intro sf _ hm
    exact close_panic_subgoal (by simp only [wp_norm, arm64_norm, *]) hm
  -- Split on `Dir::get` result `w : Except Unit (List (BitVec 8))`
  cases w with
  | error u =>
    cases u
    apply unpack_getResultAt_err
    intro fnPtr sBs sCap sPtr
    apply SepWPp.of_sepWP_ret
    apply SepWP.focus_rw (out_48_pre_split x.call.out)
    wp_pull_exists
    apply SepWP.focus_weaken (sp_152_fold_64 s0.sp _)
    wp_pull_exists
    wp_steps
    apply SepWP.focus_rw (pointsTo64_sp_152_split s0.sp _)
    wp_steps
    apply SepWP.focus_rw (sevenLo_sp_151' s0.sp _ _ _ _)
    wp_steps
    apply SepWP.focus_rw (sevenLo_sp_72' s0.sp _ _ _ _)
    wp_steps
    apply SepWP.focus_rw (sevenHi_sp_72' s0.sp _ _ _ _)
    wp_steps
    apply SepWP.focus_rw (sevenLo_sp_72' s0.sp _ _ _ _)
    wp_steps
    apply SepWP.focus_rw (sevenLo_out_41' x.call.out _ _ _ _)
    wp_steps
    apply SepWP.focus_weaken (sp_151_sevenHi_fold_7 s0.sp _ _ _ _)
    apply SepWP.focus_weaken (sp_144_cells6_fold_48 s0.sp _ _ _ _ _ _)
    refine focus_out_err_fold A x.call.out sCap sPtr sBs fnPtr (by sep_focus) ?_ ?_ ?_
    · bv_bits
    · bv_bits
    refine focus_postAns A x.call.out
      (x.peers.get rd s0.fs.files x.call.call.addr.name.bytes)
      (.error ()) (.error ()) x.call.call.key s0 (by sep_focus) ?_ ?_
    · exact post_err_disj (sf1 := sf) ⟨by assumption, by assumption⟩
        (by simp only [wp_norm, arm64_norm])
    wp_done
  | ok bs =>
    have ⟨hget, htr_get⟩ :=
      post_ok_disj (bs := bs)
        (dget := x.peers.get rd s0.fs.files x.call.call.addr.name.bytes)
        (s0 := s0) (sf1 := sf) ⟨by assumption, by assumption⟩
    have hfile : IdFileWf bs := by
      have hwf : ∀ bs, x.peers.get rd s0.fs.files x.call.call.addr.name.bytes = .ok bs →
          IdFileWf bs := by assumption
      exact hwf bs hget.symm
    cases bs with
    | nil =>
      apply unpack_getResultAt_ok
      intro bCap bPtr hbCap_le hbCap_lt hbPtr_ne
      by_cases hc0 : bCap = 0#64
      · subst hc0
        apply SepWPp.of_sepWP_ret
        apply SepWP.focus_rw (out_48_pre_split x.call.out)
        wp_pull_exists
        have hemp : ((bPtr ↦ₛ ([] : List (BitVec 8))) ∗ vecU8BufRest A 0#64 bPtr 0) = emp := by
          simp [vecU8BufRest]
        apply SepWP.focus_rw hemp
        wp_steps
        apply SepWP.focus_rw (sevenLo_sp_72' s0.sp _ _ _ _)
        wp_steps
        apply SepWP.focus_rw (sevenLo_out_41' x.call.out _ _ _ _)
        wp_steps
        apply SepWP.focus_weaken (sp_144_cells4_fold_48 s0.sp _ _ _ _)
        apply SepWP.focus_weaken
          (out_ok_fold A x.call.out true _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl)
        refine focus_postAns A x.call.out
          (x.peers.get rd s0.fs.files x.call.call.addr.name.bytes)
          (.ok []) (.ok none) x.call.call.key s0 (by sep_focus) ?_ ?_
        · exact ⟨⟨hget, by simp only [wp_norm, arm64_norm, *]⟩, rfl⟩
        wp_done
      · have hc0_beq : (bCap == 0#64) = false := beq_false_of_ne hc0
        apply SepWPp.of_sepWP_inImage
          (mid := fnBase + bv% (ls_rel%
            "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}"
            "__rustc::__rust_dealloc"))
          (by assumption)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        intro hinv_d0
        wp_call_inImage hDeallocCells hinv_d0 (bPtr, bCap, [], s0.sp - 192#64)
        case panic =>
          intro sf_p _ hm
          exact close_panic_subgoal (by simp only [wp_norm, arm64_norm, *]) hm
        apply SepWPp.of_sepWP_ret
        apply SepWP.focus_rw (out_48_pre_split x.call.out)
        wp_pull_exists
        wp_steps
        apply SepWP.focus_rw (sevenLo_sp_72' s0.sp _ _ _ _)
        wp_steps
        apply SepWP.focus_rw (sevenLo_out_41' x.call.out _ _ _ _)
        wp_steps
        apply SepWP.focus_weaken (sp_144_cells4_fold_48 s0.sp _ _ _ _)
        apply SepWP.focus_weaken
          (out_ok_fold A x.call.out true _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl)
        refine focus_postAns A x.call.out
          (x.peers.get rd s0.fs.files x.call.call.addr.name.bytes)
          (.ok []) (.ok none) x.call.call.key s0 (by sep_focus) ?_ ?_
        · exact ⟨⟨hget, by simp only [wp_norm, arm64_norm, *]⟩, rfl⟩
        wp_done
    | cons b bs' =>
      rcases hfile with hnil | ⟨ik, hser⟩
      · nomatch hnil
      · have hdec : decodeIdentityKey (b :: bs') = .ok ik :=
          hser ▸ decodeIdentityKey_serialize ik
        apply unpack_getResultAt_ok
        intro bCap bPtr hbCap_le hbCap_lt hbPtr_ne
        have hlen_lt : (b :: bs').length < 2 ^ 63 := Nat.lt_of_le_of_lt hbCap_le hbCap_lt
        have hlen_ne : BitVec.ofNat 64 (b :: bs').length ≠ 0#64 := cons_len_bv_ne_zero hlen_lt
        have hlen_beq : (BitVec.ofNat 64 (b :: bs').length == 0#64) = false :=
          beq_false_of_ne hlen_ne
        have hbCap_ne : bCap ≠ 0#64 := cap_ne_zero_of_cons hbCap_le
        have hbCap_beq : (bCap == 0#64) = false := beq_false_of_ne hbCap_ne
        -- Step `+0x44 .. +0x60` -> `IdentityKey::decode`
        apply SepWPp.of_sepWP_inImage
          (mid := fnBase - bv% (ls_rel%
            "<libsignal_protocol::identity_key::IdentityKey>::decode"
            "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}"))
          (by assumption)
        wp_steps
        apply SepWP.focus_weaken (sp_144_cells4_fold_48 s0.sp _ _ _ _)
        apply SepWP.done (by wp_norm_goal; bv_omega) (by wp_norm_lhs)
        intro hinv_dec
        wp_call_inImage hDecCells hinv_dec
          (bPtr, b :: bs', s0.sp - 144#64, ik, s0.sp - 192#64)
        case panic =>
          intro sf_p _ hm
          exact close_panic_subgoal (by simp only [wp_norm, arm64_norm, *]) hm
        -- Unpack 32-byte decoded public key at `s0.sp - 136#64`, load into regs, call `dealloc`
        rcases exists_pollKeyChunks_of_length_32 ik.publicKey.bytes.toList_length with
          ⟨kw0, kw4, kb6, kv7, kv15, kv23, kb31, hchunks⟩
        have hkey_sp136 :
            ((s0.sp - 144#64 + 8#64) ↦ₛ ik.publicKey.bytes.toList) =
              ((s0.sp - 136#64) ↦₃₂ kw0) ∗ ((s0.sp - 132#64) ↦₁₆ kw4) ∗
              ((s0.sp - 130#64) ↦₈ kb6) ∗ ((s0.sp - 129#64) ↦₆₄ kv7) ∗
              ((s0.sp - 121#64) ↦₆₄ kv15) ∗ ((s0.sp - 113#64) ↦₆₄ kv23) ∗
              ((s0.sp - 105#64) ↦₈ kb31) := by
          have ha : s0.sp - 144#64 + 8#64 = s0.sp - 136#64 := by bv_omega
          rw [ha, hchunks (s0.sp - 136#64), pollKeyChunks_sp_136]
        have hm8 : memRegion (s0.sp - 144#64 + 40#64) 8 = memRegion (s0.sp - 104#64) 8 := by
          congr 1; bv_omega
        apply SepWPp.of_sepWP_inImage
          (mid := fnBase + bv% (ls_rel%
            "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}"
            "__rustc::__rust_dealloc"))
          (by assumption)
        apply SepWP.focus_rw hkey_sp136
        apply SepWP.focus_rw hm8
        wp_steps
        apply SepWP.focus_weaken (sp_144_ikDec_fold_48 s0.sp _ _ _ _ _ _ _ _)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        intro hinv_d1
        wp_call_inImage hDeallocCells hinv_d1
          (bPtr, bCap, b :: bs', s0.sp - 192#64)
        case panic =>
          intro sf_p _ hm
          exact close_panic_subgoal (by simp only [wp_norm, arm64_norm, *]) hm
        -- Reassemble 32-byte key at `s0.sp - 144#64`, call `PublicKey::eq`
        apply SepWPp.of_sepWP_inImage
          (mid := fnBase - bv% (ls_rel%
            "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq"
            "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}"))
          (by assumption)
        apply SepWP.focus_rw (sret_48_sp_144_rebuild_split s0.sp)
        wp_pull_exists
        wp_steps
        refine focus_pollKeyChunks_sp_144 s0.sp hchunks (by sep_focus) ?_ ?_ ?_ ?_
        · bv_bits
        · bv_bits
        · bv_bits
        apply SepWP.done (by wp_norm_goal; bv_omega) (by wp_norm_lhs)
        intro hinv_eq
        wp_call_inImage hEqCells hinv_eq
          (s0.sp - 144#64, ik, x.call.call.keyA, x.call.call.key, s0.sp - 192#64)
        case panic =>
          intro sf_p _ hm
          rw [← sepConj_assoc]
          refine close_panic_subgoal ?_ hm
          simp only [wp_norm, arm64_norm, *]
        -- Write `Ok(ik == key)` into `x.call.out` and return
        apply SepWPp.of_sepWP_ret
        apply SepWP.focus_rw (out_48_pre_split x.call.out)
        wp_pull_exists
        wp_steps
        apply SepWP.focus_rw (sevenLo_sp_72' s0.sp _ _ _ _)
        wp_steps
        apply SepWP.focus_rw (sevenLo_out_41' x.call.out _ _ _ _)
        wp_steps
        apply SepWP.focus_weaken (sp_144_key_fold_48 s0.sp ik.publicKey.bytes.toList_length)
        apply SepWP.focus_weaken
          (out_ok_fold A x.call.out (decide (ik = x.call.call.key))
            _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl)
        refine focus_postAns A x.call.out
          (x.peers.get rd s0.fs.files x.call.call.addr.name.bytes)
          (.ok (b :: bs')) (.ok (some ik)) x.call.call.key s0 (by sep_focus) ?_ ?_
        · exact ⟨⟨hget, by simp only [wp_norm, arm64_norm, *]⟩, ⟨ik, rfl, hser⟩⟩
        wp_done

theorem idTrustPollInner_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {getStk : Nat}
    (hC : AllocContractsX img A ext)
    (hGet : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName)
      (dirGetSpec rd pathOk A img getStk))
    (hDec : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr RecordCodecsBinary.identityKeyDecodeName)
      (RecordCodecsBinary.identityKeyDecodeSpec A img))
    (hEq : Getters.PublicKeyEqOkExt img.base ext)
    (hhi : max (max getStk 0x60) (max 64 extHookStack) ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr idTrustPollName)
      ((cliIdTrustPollInnerSpec rd pathOk A img
        (max (max getStk 0x60) (max 64 extHookStack))).inImage img) := by
  let calleeStk := max (max getStk 0x60) (max 64 extHookStack)
  have hGetCells := dirGet_cells_ok (calleeStk := calleeStk) hGet (by omega) hhi
  have hDecCells := ikDecode_cells_ok (calleeStk := calleeStk) hDec (by omega) hhi
  have hDeallocCells := deallocVecBuf_ok (calleeStk := calleeStk) hC (by omega) hhi
  have hEqCells := pkEq_cells_ok (calleeStk := calleeStk) hEq (by omega) hhi
  rw [dirGet_fnAddr_eq] at hGetCells
  rw [identityKeyDecode_fnAddr_eq] at hDecCells
  rw [publicKeyEq_fnAddr_eq] at hEqCells
  exact idTrustPollInner_ok_of_cells hGetCells hDecCells hDeallocCells hEqCells

theorem idTrustPollInner_ok_ext32 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {getStk : Nat}
    (hC : AllocContractsX img A ext)
    (hGet : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName)
      (dirGetSpec rd pathOk A img getStk))
    (hDec : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr RecordCodecsBinary.identityKeyDecodeName)
      (RecordCodecsBinary.identityKeyDecodeSpec A img))
    (hEq : Getters.PublicKeyEqOkExt32 img.base ext)
    (hhi : max (max getStk 0x60) Getters.publicKeyEqStackExt ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr idTrustPollName)
      ((cliIdTrustPollInnerSpec rd pathOk A img
        (max (max getStk 0x60) Getters.publicKeyEqStackExt)).inImage img) := by
  let calleeStk := max (max getStk 0x60) Getters.publicKeyEqStackExt
  have hGetCells := dirGet_cells_ok (calleeStk := calleeStk) hGet (by omega) hhi
  have hDecCells := ikDecode_cells_ok (calleeStk := calleeStk) hDec (by omega) hhi
  have hDeallocCells := deallocVecBuf_ok (calleeStk := calleeStk) hC
    (by dsimp only [calleeStk, Getters.publicKeyEqStackExt]; omega) hhi
  have hEqCells := pkEq_cells_ok_ext32 (calleeStk := calleeStk) hEq (by omega) hhi
  rw [dirGet_fnAddr_eq] at hGetCells
  rw [identityKeyDecode_fnAddr_eq] at hDecCells
  rw [publicKeyEq_fnAddr_eq] at hEqCells
  exact idTrustPollInner_ok_of_cells hGetCells hDecCells hDeallocCells hEqCells

end CryptoVerification.SignalSession.Cli.Store.IdTrustPoll.Helpers
