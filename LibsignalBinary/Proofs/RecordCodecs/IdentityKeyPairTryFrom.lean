/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.Loop
import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.LoopMerge
import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.PostPk
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import ProofLib.SepLogic.WPp

/-!
# Verification of `<IdentityKeyPair as TryFrom<&[u8]>>::try_from`

Proves `<IdentityKeyPair as TryFrom<&[u8]>>::try_from` (`protocol/src/identity_key.rs:181–192`,
frame `sub sp, sp, #0xe0`) against `identityKeyPairTryFromSpec` and
`identityKeyPairTryFromPlacedSpec` (Block `84`): runs the `IdentityKeyPairStructure` protobuf merge
loop, validates field 1 via `PublicKey::try_from`, checks that field 2 has 32 bytes with inline
scalar clamping (`bfxil`), and frees both temporary `Vec<u8>` buffers on every path.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.RecordCodecsBinary.IdentityKeyPairTryFrom

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

/-- `<IdentityKeyPair as TryFrom<&[u8]>>::try_from` meets `identityKeyPairTryFromSpec` at any
4 KiB-aligned image base, given the hooks (`Stage2ContractsX`) and the proved callees
(`DecodeDeps`). -/
theorem identityKeyPairTryFrom_ok_of_deps {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsX img C A encFn decFn ext) (d : DecodeDeps img A ext)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName)
      (identityKeyPairTryFromSpec A img) := by
  let _ := hb
  exact Helpers.ikp_subroutine_ok hC d

end CryptoVerification.RecordCodecsBinary.IdentityKeyPairTryFrom

namespace CryptoVerification.RecordCodecsBinary.IdentityKeyPairTryFrom.Helpers

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.RecordCodecs
open CryptoVerification.RecordCodecsBinary

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

section TopStateSimp

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_top (s : State) (pc : BitVec 64) : (s.setPC pc).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_top (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPState_top (s : State) (ps : PState) : (s.setPState ps).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_advancePC_top (s : State) : s.advancePC.sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_writeReg64_gpr_top (s : State) (idx : BitVec 5) (val : BitVec 64) :
    (s.writeReg64 (Reg.gpr idx) val).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_writeReg32_gpr_top (s : State) (idx : BitVec 5) (val : BitVec 32) :
    (s.writeReg32 (Reg.gpr idx) val).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_writeReg_gpr_top (s : State) (w : Width) (idx : BitVec 5) (val : BitVec 64) :
    (s.writeReg w (Reg.gpr idx) val).sp = s.sp := by cases w <;> cases s <;> rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_top (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := State.readReg64_setPC s pc r
@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_top (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPState_top (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_top (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_top (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPState_top (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg32 r = s.readReg32 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_top (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_top (s : State) (m : Memory) (w : RegWidth) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPState_top (s : State) (ps : PState) (w : RegWidth) (r : Reg) :
    (s.setPState ps).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

end TopStateSimp

section Placed

open CryptoVerification.RecordCodecs.Placed

theorem mergePubKey_264_placed_cps [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) {x : DecodeGhost} {s0 s : State} {sp' ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)} {m : IdentityKeyPairStructure}
    (hpc : s.pc = (blkPl_84).base + 264#64) (hrun : s.status = .Running)
    (hregs : IkpLoopRegsPlaced s0 sp' x.ret s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat) (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (v rest : List (BitVec 8)) (s1 : State),
      mergeBytes wt bs = some (v, rest) →
      s1.pc = (blkPl_84).base + 108#64 → s1.status = .Running →
      IkpLoopRegsPlaced s0 sp' x.ret s1 →
      Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s1
        (sliceCursorAfter (sp' + 32#64) ptr bs rest ∗
          ikpLoopCommonPlaced A sp' x.ret rest.length { m with publicKey := v })
        (ikpExitPostPlaced A s0 sp' x.ret ptr bs (IdentityKeyPair.tryFrom x.bytes))
        (tryFromQp s0))
    (hnone : mergeBytes wt bs = none →
      IdentityKeyPair.tryFrom x.bytes = .error .invalidProtobufEncoding) :
    Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s
      (sliceCursorAt (sp' + 32#64) ptr bs ∗ ikpLoopCommonPlaced A sp' x.ret bs.length m)
      (ikpExitPostPlaced A s0 sp' x.ret ptr bs (IdentityKeyPair.tryFrom x.bytes))
      (tryFromQp s0) := by
  have hcall := ikp_bytesMerge_placed_ok d
  have herr := @decodeErrorPush_916_placed_wp _ A H d x s0
  unfold ikpLoopCommonPlaced ikpStructLoopOf ikpStructAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
  refine Wire.SepWPp.exists_pre fun pk => Wire.SepWPp.exists_pre fun sk =>
    Wire.SepWPp.pure_pre fun ⟨hpk_ok, hsk_ok⟩ => ?_
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
  have hsp_eq := hregs.base.sp; have _hsp_align := hregs.base.spAligned; have h29 := hregs.x29
  have hstack := stackAt_sub_split sp' bytesMergeStackX (skipFieldStackX 100)
  refine sepWPp_of_sepWP_lscro hregs.base.crl (mid := lsmpl.base 7) ?_; wp_steps
  refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
  have hregs1 := hregs.of_steps hcrl1 (by simp [*, arm64_norm])
    (by simp [*, hregs.base.trace, arm64_norm])
    (by simp [*, hregs.base.x26, arm64_norm]) (by simp [*, hregs.base.x27, arm64_norm])
    (by simp [*, hregs.base.x28, arm64_norm]) (by simp [*, arm64_norm])
    (by simp [*, hregs.x19, arm64_norm]) (by simp [*, hregs.x21, arm64_norm])
    (by simp [*, hregs.x24, arm64_norm])
  refine sepWPp_call_lscro
    ⟨wt, sp' + 48#64, pk.cap, pk.ptr, m.publicKey, sp' + 168#64, sp' + 32#64, ptr, bs⟩ hcall
    (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
    (by tryFromPost_sp_align hregs1.base.spAligned) hcrl1
    (by simp [*, arm64_norm] : _ = (blkPl_84).base + bv% (276))
    (by simp [*, hregs.base.trace, arm64_norm])
    (T := vecU8At A (sp' + 48#64) pk.cap pk.ptr m.publicKey ∗
      ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗
      sliceCursorAt (sp' + 32#64) ptr bs ∗ A.pool ∗ stackAt sp' bytesMergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      sp' + 48#64 = sp' + 48#64 ∧ sp' + 168#64 = sp' + 168#64 ∧
      bs.length < 9223372036854775808 ∧ BytesMergeCapOk pk.cap bs.length)
    (by simp [*, bytesMergeRawSpecX, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, rfl, rfl, hlen, hpk_ok⟩
    (by rw [hstack]; sep_focus) ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  dsimp only [bytesMergeRawSpecX]
  cases hm : mergeBytes wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩
    dsimp only
    obtain ⟨k, _, hrest, _⟩ := mergeBytes_suffix hm
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    rw [sepConj_assoc]; refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hx0_0 => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun cap' => Wire.SepWPp.exists_pre fun ptr' => ?_
    simp only [sepConj_pure_left_comm]; refine Wire.SepWPp.pure_pre fun hcap' => ?_
    have hregs2 := hregs1.of_calleeSaved hsp2 hsp2_align hcrl2 (htr2.trans hregs1.base.trace) hcs2
    have _hsp2_eq := hregs2.base.sp; have _hsp2_align := hregs2.base.spAligned
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_84).base + bv% (108)) ?_; wp_steps
    refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl3
    have hstruct : vecU8At A (sp' + 48#64) cap' ptr' v ∗
        vecU8At A (sp' + 72#64) sk.cap sk.ptr m.privateKey ⊢
        ikpStructLoopOf A (sp' + 48#64) rest.length { m with publicKey := v } := by
      simpa [ikpStructAt, BitVec.add_assoc] using
        ikpStructAt_entails_loopOf A ⟨cap', ptr'⟩ sk (sp' + 48#64) rest.length
          { m with publicKey := v } hcap' (bytesMergeCapOk_mono hsk_ok hrest_le)
    refine Wire.SepWPp.mono_pre
      (P' := sliceCursorAfter (sp' + 32#64) ptr bs rest ∗
        ikpLoopCommonPlaced A sp' x.ret rest.length { m with publicKey := v })
      (by unfold ikpLoopCommonPlaced
          refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstruct)))
          apply entails_of_eq; try rw [hstack]
          try rw [hregs1.base.sp]; try rw [hregs2.base.sp]
          try simp only [arm64_norm]; ac_rfl) ?_
    exact hcont v rest _ hm (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      (hregs2.of_steps hcrl3 (by simp [*, hregs2.base.sp, arm64_norm])
        (by simp [*, hregs2.base.trace, arm64_norm]) (by simp [*, hregs2.base.x26, arm64_norm])
        (by simp [*, hregs2.base.x27, arm64_norm]) (by simp [*, hregs2.base.x28, arm64_norm])
        (by simp [*, hregs2.x29, arm64_norm]) (by simp [*, hregs2.x19, arm64_norm])
        (by simp [*, hregs2.x21, arm64_norm]) (by simp [*, hregs2.x24, arm64_norm]))
  | none =>
    dsimp only; rw [sepConj_assoc]; refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hx0_ne => ?_
    have hregs2 := hregs1.of_calleeSaved hsp2 hsp2_align hcrl2 (htr2.trans hregs1.base.trace) hcs2
    have _hsp2_eq := hregs2.base.sp; have _hsp2_align := hregs2.base.spAligned
    have _hx29_2 := hregs2.x29
    have _hne : (s2.readReg64 .x0 == 0#64) = false := beq_false_of_ne hx0_ne
    rw [ikpMem48_split8 sp', ProofLib.memRegion_eight (sp' + 96#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun w0 => ?_
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_84).base + bv% (916)) ?_; wp_steps
    refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl3
    have hstruct : vecU8At A (sp' + 48#64) pk.cap pk.ptr m.publicKey ∗
        vecU8At A (sp' + 72#64) sk.cap sk.ptr m.privateKey ⊢ ikpStructOf A (sp' + 48#64) m := by
      simpa [ikpStructAt, BitVec.add_assoc] using ikpStructAt_entails_of A pk sk (sp' + 48#64) m
    refine Wire.SepWPp.mono_pre
      (P' := memRegion sp' 32 ∗ memRegion (sp' + 32#64) 16 ∗ ikpStructOf A (sp' + 48#64) m ∗
        ((sp' + 96#64) ↦₆₄ s2.readReg64 (Reg.gpr 0#5)) ∗ memRegion (sp' + 104#64) 40 ∗
        ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗ memRegion x.ret 72 ∗ (ptr ↦ₛ bs) ∗ lsLogOff ∗ A.pool ∗
        stackAt sp' (skipFieldStackX 100) ∗ decodeErrorAtStackLen A (s2.readReg64 (Reg.gpr 0#5)) 0)
      (by refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstruct)))
          apply entails_of_eq; try rw [hstack]
          try rw [hregs1.base.sp]; try rw [hregs2.base.sp]
          try simp only [arm64_norm]; ac_rfl) ?_
    exact herr (hnone hm)
      (hregs2.of_steps hcrl3 (by simp [*, hregs2.base.sp, arm64_norm])
        (by simp [*, hregs2.base.trace, arm64_norm]) (by simp [*, hregs2.base.x26, arm64_norm])
        (by simp [*, hregs2.base.x27, arm64_norm]) (by simp [*, hregs2.base.x28, arm64_norm])
        (by simp [*, hregs2.x29, arm64_norm]) (by simp [*, hregs2.x19, arm64_norm])
        (by simp [*, hregs2.x21, arm64_norm]) (by simp [*, hregs2.x24, arm64_norm]))
      (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      (by simp [*, arm64_norm]) hx0_ne (by decide)

theorem mergePrivKey_92_placed_cps [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) {x : DecodeGhost} {s0 s : State} {sp' ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)} {m : IdentityKeyPairStructure}
    (hpc : s.pc = (blkPl_84).base + 92#64) (hrun : s.status = .Running)
    (hregs : IkpLoopRegsPlaced s0 sp' x.ret s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat) (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (v rest : List (BitVec 8)) (s1 : State),
      mergeBytes wt bs = some (v, rest) →
      s1.pc = (blkPl_84).base + 108#64 → s1.status = .Running →
      IkpLoopRegsPlaced s0 sp' x.ret s1 →
      Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s1
        (sliceCursorAfter (sp' + 32#64) ptr bs rest ∗
          ikpLoopCommonPlaced A sp' x.ret rest.length { m with privateKey := v })
        (ikpExitPostPlaced A s0 sp' x.ret ptr bs (IdentityKeyPair.tryFrom x.bytes))
        (tryFromQp s0))
    (hnone : mergeBytes wt bs = none →
      IdentityKeyPair.tryFrom x.bytes = .error .invalidProtobufEncoding) :
    Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s
      (sliceCursorAt (sp' + 32#64) ptr bs ∗ ikpLoopCommonPlaced A sp' x.ret bs.length m)
      (ikpExitPostPlaced A s0 sp' x.ret ptr bs (IdentityKeyPair.tryFrom x.bytes))
      (tryFromQp s0) := by
  have hcall := ikp_bytesMerge_placed_ok d
  have herr := @decodeErrorPush_916_placed_wp _ A H d x s0
  unfold ikpLoopCommonPlaced ikpStructLoopOf ikpStructAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
  refine Wire.SepWPp.exists_pre fun pk => Wire.SepWPp.exists_pre fun sk =>
    Wire.SepWPp.pure_pre fun ⟨hpk_ok, hsk_ok⟩ => ?_
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
  have hsp_eq := hregs.base.sp; have _hsp_align := hregs.base.spAligned
  have h29 := hregs.x29; have h21 := hregs.x21
  have hstack := stackAt_sub_split sp' bytesMergeStackX (skipFieldStackX 100)
  refine sepWPp_of_sepWP_lscro hregs.base.crl (mid := lsmpl.base 7) ?_; wp_steps
  refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
  have hregs1 := hregs.of_steps hcrl1 (by simp [*, arm64_norm])
    (by simp [*, hregs.base.trace, arm64_norm])
    (by simp [*, hregs.base.x26, arm64_norm]) (by simp [*, hregs.base.x27, arm64_norm])
    (by simp [*, hregs.base.x28, arm64_norm]) (by simp [*, arm64_norm])
    (by simp [*, hregs.x19, arm64_norm]) (by simp [*, arm64_norm])
    (by simp [*, hregs.x24, arm64_norm])
  refine sepWPp_call_lscro
    ⟨wt, sp' + 72#64, sk.cap, sk.ptr, m.privateKey, sp' + 168#64, sp' + 32#64, ptr, bs⟩ hcall
    (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
    (by tryFromPost_sp_align hregs1.base.spAligned) hcrl1
    (by simp [*, arm64_norm] : _ = (blkPl_84).base + bv% (104))
    (by simp [*, hregs.base.trace, arm64_norm])
    (T := vecU8At A (sp' + 72#64) sk.cap sk.ptr m.privateKey ∗
      ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗
      sliceCursorAt (sp' + 32#64) ptr bs ∗ A.pool ∗ stackAt sp' bytesMergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      sp' + 72#64 = sp' + 72#64 ∧ sp' + 168#64 = sp' + 168#64 ∧
      bs.length < 9223372036854775808 ∧ BytesMergeCapOk sk.cap bs.length)
    (by simp [*, bytesMergeRawSpecX, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, rfl, rfl, hlen, hsk_ok⟩
    (by rw [hstack]; sep_focus) ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  dsimp only [bytesMergeRawSpecX]
  cases hm : mergeBytes wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩
    dsimp only
    obtain ⟨k, _, hrest, _⟩ := mergeBytes_suffix hm
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    rw [sepConj_assoc]; refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hx0_0 => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun cap' => Wire.SepWPp.exists_pre fun ptr' => ?_
    simp only [sepConj_pure_left_comm]; refine Wire.SepWPp.pure_pre fun hcap' => ?_
    have hregs2 := hregs1.of_calleeSaved hsp2 hsp2_align hcrl2 (htr2.trans hregs1.base.trace) hcs2
    have _hsp2_eq := hregs2.base.sp; have _hsp2_align := hregs2.base.spAligned
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_84).base + bv% (108)) ?_; wp_steps
    refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl3
    have hstruct : vecU8At A (sp' + 48#64) pk.cap pk.ptr m.publicKey ∗
        vecU8At A (sp' + 72#64) cap' ptr' v ⊢
        ikpStructLoopOf A (sp' + 48#64) rest.length { m with privateKey := v } := by
      simpa [ikpStructAt, BitVec.add_assoc] using
        ikpStructAt_entails_loopOf A pk ⟨cap', ptr'⟩ (sp' + 48#64) rest.length
          { m with privateKey := v } (bytesMergeCapOk_mono hpk_ok hrest_le) hcap'
    refine Wire.SepWPp.mono_pre
      (P' := sliceCursorAfter (sp' + 32#64) ptr bs rest ∗
        ikpLoopCommonPlaced A sp' x.ret rest.length { m with privateKey := v })
      (by unfold ikpLoopCommonPlaced
          refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstruct)))
          apply entails_of_eq; try rw [hstack]
          try rw [hregs1.base.sp]; try rw [hregs2.base.sp]
          try simp only [arm64_norm]; ac_rfl) ?_
    exact hcont v rest _ hm (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      (hregs2.of_steps hcrl3 (by simp [*, hregs2.base.sp, arm64_norm])
        (by simp [*, hregs2.base.trace, arm64_norm]) (by simp [*, hregs2.base.x26, arm64_norm])
        (by simp [*, hregs2.base.x27, arm64_norm]) (by simp [*, hregs2.base.x28, arm64_norm])
        (by simp [*, hregs2.x29, arm64_norm]) (by simp [*, hregs2.x19, arm64_norm])
        (by simp [*, hregs2.x21, arm64_norm]) (by simp [*, hregs2.x24, arm64_norm]))
  | none =>
    dsimp only; rw [sepConj_assoc]; refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hx0_ne => ?_
    have hregs2 := hregs1.of_calleeSaved hsp2 hsp2_align hcrl2 (htr2.trans hregs1.base.trace) hcs2
    have _hsp2_eq := hregs2.base.sp; have _hsp2_align := hregs2.base.spAligned
    have _hx29_2 := hregs2.x29
    have _hne : (s2.readReg64 .x0 == 0#64) = false := beq_false_of_ne hx0_ne
    rw [ikpMem48_split8 sp', ProofLib.memRegion_eight (sp' + 96#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun w0 => ?_
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_84).base + bv% (916)) ?_; wp_steps
    refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl3
    have hstruct : vecU8At A (sp' + 48#64) pk.cap pk.ptr m.publicKey ∗
        vecU8At A (sp' + 72#64) sk.cap sk.ptr m.privateKey ⊢ ikpStructOf A (sp' + 48#64) m := by
      simpa [ikpStructAt, BitVec.add_assoc] using ikpStructAt_entails_of A pk sk (sp' + 48#64) m
    refine Wire.SepWPp.mono_pre
      (P' := memRegion sp' 32 ∗ memRegion (sp' + 32#64) 16 ∗ ikpStructOf A (sp' + 48#64) m ∗
        ((sp' + 96#64) ↦₆₄ s2.readReg64 (Reg.gpr 0#5)) ∗ memRegion (sp' + 104#64) 40 ∗
        ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗ memRegion x.ret 72 ∗ (ptr ↦ₛ bs) ∗ lsLogOff ∗ A.pool ∗
        stackAt sp' (skipFieldStackX 100) ∗ decodeErrorAtStackLen A (s2.readReg64 (Reg.gpr 0#5)) 0)
      (by refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstruct)))
          apply entails_of_eq; try rw [hstack]
          try rw [hregs1.base.sp]; try rw [hregs2.base.sp]
          try simp only [arm64_norm]; ac_rfl) ?_
    exact herr (hnone hm)
      (hregs2.of_steps hcrl3 (by simp [*, hregs2.base.sp, arm64_norm])
        (by simp [*, hregs2.base.trace, arm64_norm]) (by simp [*, hregs2.base.x26, arm64_norm])
        (by simp [*, hregs2.base.x27, arm64_norm]) (by simp [*, hregs2.base.x28, arm64_norm])
        (by simp [*, hregs2.x29, arm64_norm]) (by simp [*, hregs2.x19, arm64_norm])
        (by simp [*, hregs2.x21, arm64_norm]) (by simp [*, hregs2.x24, arm64_norm]))
      (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      (by simp [*, arm64_norm]) hx0_ne (by decide)

theorem mergeSkipField_284_placed_cps [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) {x : DecodeGhost} {s0 s : State} {sp' ptr : BitVec 64}
    {tag : ℕ} {wt : WireType} {bs : List (BitVec 8)} {m : IdentityKeyPairStructure}
    (hpc : s.pc = (blkPl_84).base + 284#64) (hrun : s.status = .Running)
    (hregs : IkpLoopRegsPlaced s0 sp' x.ret s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag)
    (htag_lt : tag < 2 ^ 32) (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (rest : List (BitVec 8)) (s1 : State),
      skipField (2 * bs.length + 2) 100 tag wt bs = some rest →
      s1.pc = (blkPl_84).base + 108#64 → s1.status = .Running →
      IkpLoopRegsPlaced s0 sp' x.ret s1 →
      Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s1
        (sliceCursorAfter (sp' + 32#64) ptr bs rest ∗ ikpLoopCommonPlaced A sp' x.ret rest.length m)
        (ikpExitPostPlaced A s0 sp' x.ret ptr bs (IdentityKeyPair.tryFrom x.bytes))
        (tryFromQp s0))
    (hnone : skipField (2 * bs.length + 2) 100 tag wt bs = none →
      IdentityKeyPair.tryFrom x.bytes = .error .invalidProtobufEncoding) :
    Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s
      (sliceCursorAt (sp' + 32#64) ptr bs ∗ ikpLoopCommonPlaced A sp' x.ret bs.length m)
      (ikpExitPostPlaced A s0 sp' x.ret ptr bs (IdentityKeyPair.tryFrom x.bytes))
      (tryFromQp s0) := by
  have hcall := ikp_skipField_placed_ok d
  have herr := @decodeErr_616_placed_wp _ A H d x s0
  unfold ikpLoopCommonPlaced
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
  have hsp_eq := hregs.base.sp; have _hsp_align := hregs.base.spAligned; have h29 := hregs.x29
  refine sepWPp_of_sepWP_lscro hregs.base.crl (mid := lsmpl.base 1) ?_; wp_steps
  refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
  have hregs1 := hregs.of_steps hcrl1 (by simp [*, arm64_norm])
    (by simp [*, hregs.base.trace, arm64_norm])
    (by simp [*, hregs.base.x26, arm64_norm]) (by simp [*, hregs.base.x27, arm64_norm])
    (by simp [*, hregs.base.x28, arm64_norm]) (by simp [*, arm64_norm])
    (by simp [*, hregs.x19, arm64_norm]) (by simp [*, hregs.x21, arm64_norm])
    (by simp [*, hregs.x24, arm64_norm])
  refine sepWPp_call_lscro ⟨wt, tag, 100, sp' + 168#64, sp' + 32#64, ptr, bs⟩ hcall
    (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
    (by tryFromPost_sp_align hregs1.base.spAligned) hcrl1
    (by simp [*, arm64_norm] : _ = (blkPl_84).base + bv% (296))
    (by simp [*, hregs.base.trace, arm64_norm])
    (T := ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗ sliceCursorAt (sp' + 32#64) ptr bs ∗
      A.pool ∗ stackAt sp' (skipFieldStackX 100))
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      (BitVec.ofNat 64 tag).setWidth 32 = BitVec.ofNat 32 tag ∧ tag < 4294967296 ∧
      sp' + 168#64 = sp' + 168#64 ∧
      (100#64 : BitVec 64).setWidth 32 = 100#32 ∧ 100 < 4294967296 ∧ bs.length < 9223372036854775808)
    (by simp [*, skipFieldSpecX, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, setWidth32_ofNat64 tag, htag_lt, rfl, rfl, by decide, hlen⟩
    (by sep_focus) ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  dsimp only [skipFieldSpecX]
  cases hs : skipField (2 * bs.length + 2) 100 tag wt bs with
  | some rest =>
    dsimp only
    obtain ⟨k, _, hrest⟩ := skipField_suffix hs
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    rw [sepConj_assoc]; refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hx0_0 => ?_
    have hregs2 := hregs1.of_calleeSaved hsp2 hsp2_align hcrl2 (htr2.trans hregs1.base.trace) hcs2
    have _hsp2_eq := hregs2.base.sp; have _hsp2_align := hregs2.base.spAligned
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_84).base + bv% (108)) ?_; wp_steps
    refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl3
    refine Wire.SepWPp.mono_pre
      (P' := sliceCursorAfter (sp' + 32#64) ptr bs rest ∗ ikpLoopCommonPlaced A sp' x.ret rest.length m)
      (by unfold ikpLoopCommonPlaced
          refine Entails.trans ?_
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
              (ikpStructLoopOf_mono A (sp' + 48#64) m hrest_le))))
          apply entails_of_eq; rw [hregs1.base.sp]; try simp only [arm64_norm]
          ac_rfl) ?_
    exact hcont rest _ hs (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      (hregs2.of_steps hcrl3 (by simp [*, hregs2.base.sp, arm64_norm])
        (by simp [*, hregs2.base.trace, arm64_norm]) (by simp [*, hregs2.base.x26, arm64_norm])
        (by simp [*, hregs2.base.x27, arm64_norm]) (by simp [*, hregs2.base.x28, arm64_norm])
        (by simp [*, hregs2.x29, arm64_norm]) (by simp [*, hregs2.x19, arm64_norm])
        (by simp [*, hregs2.x21, arm64_norm]) (by simp [*, hregs2.x24, arm64_norm]))
  | none =>
    dsimp only; rw [sepConj_assoc]; refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hx0_ne => ?_
    have hregs2 := hregs1.of_calleeSaved hsp2 hsp2_align hcrl2 (htr2.trans hregs1.base.trace) hcs2
    have _hsp2_eq := hregs2.base.sp
    have _hne : (s2.readReg64 .x0 == 0#64) = false := beq_false_of_ne hx0_ne
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_84).base + bv% (616)) ?_; wp_steps
    refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl3
    refine Wire.SepWPp.mono_pre
      (P' := memRegion sp' 32 ∗ memRegion (sp' + 32#64) 16 ∗ ikpStructOf A (sp' + 48#64) m ∗
        memRegion (sp' + 96#64) 48 ∗ ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗
        memRegion x.ret 72 ∗ (ptr ↦ₛ bs) ∗ lsLogOff ∗ A.pool ∗
        stackAt sp' (skipFieldStackX 100) ∗ decodeErrorAt A (s2.readReg64 (Reg.gpr 0#5)))
      (by refine Entails.trans ?_
            (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono (ikpStructLoopOf_entails_of A (sp' + 48#64) bs.length m)
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                    (decodeErrorWith_entails_at A (s2.readReg64 (Reg.gpr 0#5)) 0)))))))))))
          apply entails_of_eq; rw [hregs1.base.sp]; try simp only [arm64_norm]
          ac_rfl) ?_
    exact herr (hnone hs)
      (hregs2.base.of_steps hcrl3 (by simp [*, hregs2.base.sp, arm64_norm])
        (by simp [*, hregs2.base.trace, arm64_norm]) (by simp [*, hregs2.base.x26, arm64_norm])
        (by simp [*, hregs2.base.x27, arm64_norm]) (by simp [*, hregs2.base.x28, arm64_norm]))
      (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      (by simp [*, hregs2.x19, arm64_norm]) (by simp [*, hregs2.x24, arm64_norm])
      (by simp [*, arm64_norm])

theorem dispatch_tag_248_placed_cps [LibsignalPlacement] {H : LibsignalHooks}
    {s0 s : State} {sp' ret : BitVec 64} {tag : ℕ}
    {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_84).base + 248#64) (hrun : s.status = .Running)
    (hregs : IkpLoopRegsPlaced s0 sp' ret s)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag)
    (htag_ge : 1 ≤ tag) (htag_lt : tag < 2 ^ 32)
    (h1 : tag = 1 → ∀ s1 : State,
      s1.pc = (blkPl_84).base + 264#64 → s1.status = .Running → IkpLoopRegsPlaced s0 sp' ret s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s1 P Q (tryFromQp s0))
    (h2 : tag = 2 → ∀ s1 : State,
      s1.pc = (blkPl_84).base + 92#64 → s1.status = .Running → IkpLoopRegsPlaced s0 sp' ret s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s1 P Q (tryFromQp s0))
    (h3 : 3 ≤ tag → ∀ s1 : State,
      s1.pc = (blkPl_84).base + 284#64 → s1.status = .Running → IkpLoopRegsPlaced s0 sp' ret s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 → s1.readReg64 .x1 = BitVec.ofNat 64 tag →
      Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s1 P Q (tryFromQp s0)) :
    Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s P Q (tryFromQp s0) := by
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
  have _hsp_eq := hregs.base.sp; have _hsp_align := hregs.base.spAligned
  rcases tag with _ | _ | _ | n
  · omega
  · refine sepWPp_of_sepWP_lscro hregs.base.crl (mid := (blkPl_84).base + bv% (264)) ?_; wp_steps
    refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
    exact h1 rfl _ (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      (hregs.of_steps hcrl1 (by simp [*, hregs.base.sp, arm64_norm])
        (by simp [*, hregs.base.trace, arm64_norm]) (by simp [*, hregs.base.x26, arm64_norm])
        (by simp [*, hregs.base.x27, arm64_norm]) (by simp [*, hregs.base.x28, arm64_norm])
        (by simp [*, hregs.x29, arm64_norm]) (by simp [*, hregs.x19, arm64_norm])
        (by simp [*, hregs.x21, arm64_norm]) (by simp [*, hregs.x24, arm64_norm]))
      (by simp [*, arm64_norm])
  · refine sepWPp_of_sepWP_lscro hregs.base.crl (mid := (blkPl_84).base + bv% (92)) ?_; wp_steps
    refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
    exact h2 rfl _ (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      (hregs.of_steps hcrl1 (by simp [*, hregs.base.sp, arm64_norm])
        (by simp [*, hregs.base.trace, arm64_norm]) (by simp [*, hregs.base.x26, arm64_norm])
        (by simp [*, hregs.base.x27, arm64_norm]) (by simp [*, hregs.base.x28, arm64_norm])
        (by simp [*, hregs.x29, arm64_norm]) (by simp [*, hregs.x19, arm64_norm])
        (by simp [*, hregs.x21, arm64_norm]) (by simp [*, hregs.x24, arm64_norm]))
      (by simp [*, arm64_norm])
  · obtain ⟨hc2, hc1, hc1_ne⟩ := tag_ge3_conds (n + 3) (by omega) htag_lt
    refine sepWPp_of_sepWP_lscro hregs.base.crl (mid := (blkPl_84).base + bv% (284)) ?_; wp_steps
    refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
    exact h3 (by omega) _ (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      (hregs.of_steps hcrl1 (by simp [*, hregs.base.sp, arm64_norm])
        (by simp [*, hregs.base.trace, arm64_norm]) (by simp [*, hregs.base.x26, arm64_norm])
        (by simp [*, hregs.base.x27, arm64_norm]) (by simp [*, hregs.base.x28, arm64_norm])
        (by simp [*, hregs.x29, arm64_norm]) (by simp [*, hregs.x19, arm64_norm])
        (by simp [*, hregs.x21, arm64_norm]) (by simp [*, hregs.x24, arm64_norm]))
      (by simp [*, arm64_norm]) (by simp [*, arm64_norm])

theorem mergeField_248_placed_cps [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) {x : DecodeGhost} {s0 s : State} {sp' ptr : BitVec 64}
    {tag : ℕ} {wt : WireType} {bs : List (BitVec 8)} {m : IdentityKeyPairStructure}
    (hpc : s.pc = (blkPl_84).base + 248#64) (hrun : s.status = .Running)
    (hregs : IkpLoopRegsPlaced s0 sp' x.ret s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag)
    (htag_ge : 1 ≤ tag) (htag_lt : tag < 2 ^ 32) (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (m' : IdentityKeyPairStructure) (rest : List (BitVec 8)) (s1 : State),
      IdentityKeyPairStructure.mergeField m tag wt bs = some (m', rest) →
      s1.pc = (blkPl_84).base + 108#64 → s1.status = .Running →
      IkpLoopRegsPlaced s0 sp' x.ret s1 →
      Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s1
        (sliceCursorAfter (sp' + 32#64) ptr bs rest ∗ ikpLoopCommonPlaced A sp' x.ret rest.length m')
        (ikpExitPostPlaced A s0 sp' x.ret ptr bs (IdentityKeyPair.tryFrom x.bytes))
        (tryFromQp s0))
    (hnone : IdentityKeyPairStructure.mergeField m tag wt bs = none →
      IdentityKeyPair.tryFrom x.bytes = .error .invalidProtobufEncoding) :
    Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s
      (sliceCursorAt (sp' + 32#64) ptr bs ∗ ikpLoopCommonPlaced A sp' x.ret bs.length m)
      (ikpExitPostPlaced A s0 sp' x.ret ptr bs (IdentityKeyPair.tryFrom x.bytes))
      (tryFromQp s0) := by
  refine dispatch_tag_248_placed_cps hpc hrun hregs hx1 htag_ge htag_lt
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hx1_1 => ?_)
  · subst htag
    exact mergePubKey_264_placed_cps d hpc1 hrun1 hregs1 (hx0_1.trans hx0) hlen
      (fun v rest s2 hm => hcont { m with publicKey := v } rest s2
        (by simp [IdentityKeyPairStructure.mergeField, hm]))
      (fun hm => hnone (by simp [IdentityKeyPairStructure.mergeField, hm]))
  · subst htag
    exact mergePrivKey_92_placed_cps d hpc1 hrun1 hregs1 (hx0_1.trans hx0) hlen
      (fun v rest s2 hm => hcont { m with privateKey := v } rest s2
        (by simp [IdentityKeyPairStructure.mergeField, hm]))
      (fun hm => hnone (by simp [IdentityKeyPairStructure.mergeField, hm]))
  · rcases Nat.exists_eq_add_of_le' htag with ⟨n, rfl⟩
    exact mergeSkipField_284_placed_cps d hpc1 hrun1 hregs1 (hx0_1.trans hx0) hx1_1 htag_lt hlen
      (fun rest s2 hs => hcont m rest s2
        (by simp [IdentityKeyPairStructure.mergeField, skipUnknown, recursionLimit, hs]))
      (fun hs => hnone (by simp [IdentityKeyPairStructure.mergeField, skipUnknown, recursionLimit, hs]))

theorem loopExit_708_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) {x : DecodeGhost} {s0 s : State} {sp' ptr : BitVec 64}
    {m : IdentityKeyPairStructure}
    (hlt : x.bytes.length < 2 ^ 32) (hdec : IdentityKeyPairStructure.decode x.bytes = some m)
    (hpc : s.pc = (blkPl_84).base + 708#64) (hrun : s.status = .Running)
    (hregs : IkpLoopRegsPlaced s0 sp' x.ret s) :
    Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s
      (sliceCursorAt (sp' + 32#64) ptr [] ∗ ikpLoopCommonPlaced A sp' x.ret 0 m)
      (ikpExitPostPlaced A s0 sp' x.ret ptr [] (IdentityKeyPair.tryFrom x.bytes))
      (tryFromQp s0) := by
  have hpost := @post_344_placed_wp _ A H d x s0
  obtain ⟨hpk_le, hsk_le⟩ := ikp_decode_field_lengths hdec
  unfold sliceCursorAt ikpLoopCommonPlaced ikpStructLoopOf ikpStructAt
  simp only [vecU8At_eq_header_buf, vecHeader, BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
  refine Wire.SepWPp.exists_pre fun pk => Wire.SepWPp.exists_pre fun sk =>
    Wire.SepWPp.pure_pre fun _ => ?_
  refine Wire.SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
        (vecU8Buf_cap_lt63 A pk.cap pk.ptr m.publicKey))))))))) ?_
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  refine Wire.SepWPp.pure_pre fun hpk_lt63 => ?_
  have ⟨hc1, hc2⟩ := cmn_one_ne_of_lt pk.cap hpk_lt63
  have hsp_eq := hregs.base.sp; subst hsp_eq
  let sp' := s.sp; have _hsp_align := hregs.base.spAligned
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
  refine sepWPp_of_sepWP_lscro hregs.base.crl (mid := (blkPl_84).base + bv% (344)) ?_; wp_steps
  refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
  have hm16 := pointsTo64_pair_entails_memRegion16 (sp' + 32#64) ptr 0#64
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm16
  have h144 := ikpFold144 sp' pk.cap pk.ptr (BitVec.ofNat 64 m.publicKey.length)
    sk.cap sk.ptr (BitVec.ofNat 64 m.privateKey.length)
  dsimp only [vecHeader] at h144; simp only [BitVec.add_assoc, BitVec.reduceAdd] at h144
  refine Wire.SepWPp.mono_pre
    (P' := (memRegion sp' 32 ∗ memRegion (sp' + 96#64) 48 ∗ memRegion x.ret 72 ∗
      vecU8Buf A pk.cap pk.ptr m.publicKey ∗ vecU8Buf A sk.cap sk.ptr m.privateKey ∗
      lsLogOff ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100)) ∗
      (memRegion (sp' + 32#64) 16 ∗ ((sp' + 48#64) ↦₆₄ pk.cap) ∗ ((sp' + 56#64) ↦₆₄ pk.ptr) ∗
        ((sp' + 64#64) ↦₆₄ BitVec.ofNat 64 m.publicKey.length) ∗
        ((sp' + 72#64) ↦₆₄ sk.cap) ∗ ((sp' + 80#64) ↦₆₄ sk.ptr) ∗
        ((sp' + 88#64) ↦₆₄ BitVec.ofNat 64 m.privateKey.length) ∗
        ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗ (ptr ↦ₛ [])))
    (by refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_left hm16))
        apply entails_of_eq
        try dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x29, Reg.x30]
        try simp only [BitVec.add_assoc]
        try simp only [BitVec.reduceAdd]
        try simp only [bv_sub_add_lit]
        try simp only [BitVec.add_assoc]
        try simp only [BitVec.reduceAdd]
        try simp only [bv_sub_add_lit]
        try simp only [arm64_norm]
        ac_rfl) ?_
  refine Wire.SepWPp.frame_tryFrom
    (Q' := fun sf Pf => IkpBaseStatePlaced s0 sp' sf ∧
      (Pf ⊢ memRegion sp' 32 ∗ memRegion (sp' + 96#64) 48 ∗
        identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
        lsLogOff ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100)))
    (hpost hdec (by omega) (by omega)
      (hregs.base.of_steps hcrl1 (by simp [*, arm64_norm])
        (by simp [*, hregs.base.trace, arm64_norm]) (by simp [*, hregs.base.x26, arm64_norm])
        (by simp [*, hregs.base.x27, arm64_norm]) (by simp [*, hregs.base.x28, arm64_norm]))
      (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      (by simp [*, hregs.x19, arm64_norm]) (by simp [*, hregs.x29, arm64_norm]; rfl)
      (by simp [*, hregs.x24, arm64_norm]) (by simp [*, arm64_norm])
      (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      (by simp [*, arm64_norm]))
    fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
  unfold ikpExitMemPlaced
  refine Entails.trans (sepConj_mono_left hentf) ?_
  refine Entails.trans ?_ (sepConj_mono_left h144)
  apply entails_of_eq
  try dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x29, Reg.x30]
  try simp only [BitVec.add_assoc]
  try simp only [BitVec.reduceAdd]
  try simp only [bv_sub_add_lit]
  try simp only [BitVec.add_assoc]
  try simp only [BitVec.reduceAdd]
  try simp only [bv_sub_add_lit]
  try simp only [arm64_norm]
  ac_rfl

theorem loopCheck_108_empty_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) {x : DecodeGhost} {s0 s : State} {sp' ptr : BitVec 64}
    {m : IdentityKeyPairStructure}
    (hlt : x.bytes.length < 2 ^ 32) (hdec : IdentityKeyPairStructure.decode x.bytes = some m)
    (hpc : s.pc = (blkPl_84).base + 108#64) (hrun : s.status = .Running)
    (hregs : IkpLoopRegsPlaced s0 sp' x.ret s) :
    Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s
      (sliceCursorAt (sp' + 32#64) ptr [] ∗
        ikpLoopCommonPlaced A sp' x.ret ([] : List (BitVec 8)).length m)
      (ikpExitPostPlaced A s0 sp' x.ret ptr [] (IdentityKeyPair.tryFrom x.bytes))
      (tryFromQp s0) := by
  have hexit := @loopExit_708_placed_wp _ A H d x s0
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
  have _hsp_eq := hregs.base.sp; have _hsp_align := hregs.base.spAligned; have _h29 := hregs.x29
  unfold sliceCursorAt ikpLoopCommonPlaced
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine sepWPp_of_sepWP_lscro hregs.base.crl (mid := (blkPl_84).base + bv% (708)) ?_; wp_steps
  refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
  refine Wire.SepWPp.mono_pre
    (P' := sliceCursorAt (sp' + 32#64) ptr [] ∗ ikpLoopCommonPlaced A sp' x.ret 0 m)
    (by unfold sliceCursorAt ikpLoopCommonPlaced; apply entails_of_eq
        try dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x29, Reg.x30]
        try simp only [BitVec.add_assoc]
        try simp only [BitVec.reduceAdd]
        try simp only [bv_sub_add_lit]
        try simp only [BitVec.add_assoc]
        try simp only [BitVec.reduceAdd]
        try simp only [bv_sub_add_lit]
        try simp only [arm64_norm]
        ac_rfl) ?_
  exact hexit hlt hdec (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
    (hregs.of_steps hcrl1 (by simp [*, hregs.base.sp, arm64_norm])
      (by simp [*, hregs.base.trace, arm64_norm]) (by simp [*, hregs.base.x26, arm64_norm])
      (by simp [*, hregs.base.x27, arm64_norm]) (by simp [*, hregs.base.x28, arm64_norm])
      (by simp [*, hregs.x29, arm64_norm]) (by simp [*, hregs.x19, arm64_norm])
      (by simp [*, hregs.x21, arm64_norm]) (by simp [*, hregs.x24, arm64_norm]))

theorem loopCheck_108_cons_placed_cps [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {x : DecodeGhost} {s0 s : State} {sp' ptr : BitVec 64}
    {b0 : BitVec 8} {bs1 : List (BitVec 8)} {m : IdentityKeyPairStructure}
    {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_84).base + 108#64) (hrun : s.status = .Running)
    (hregs : IkpLoopRegsPlaced s0 sp' x.ret s) (hlen : (b0 :: bs1).length < 2 ^ 63)
    (hcont : ∀ s1 : State,
      s1.pc = (blkPl_84).base + 124#64 → s1.status = .Running →
      IkpLoopRegsPlaced s0 sp' x.ret s1 →
      s1.readReg64 .x23 = sp' + 32#64 → s1.readReg64 .x22 = sp' + 40#64 →
      s1.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length →
      Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s1
        (sliceCursorAt (sp' + 32#64) ptr (b0 :: bs1) ∗
          ikpLoopCommonPlaced A sp' x.ret (b0 :: bs1).length m) Q (tryFromQp s0)) :
    Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s
      (sliceCursorAt (sp' + 32#64) ptr (b0 :: bs1) ∗
        ikpLoopCommonPlaced A sp' x.ret (b0 :: bs1).length m) Q (tryFromQp s0) := by
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
  have _hsp_eq := hregs.base.sp; have _hsp_align := hregs.base.spAligned; have _h29 := hregs.x29
  obtain ⟨hc_eq, hc_ne⟩ := cons_len_bv64_ne_zero b0 bs1 hlen
  unfold sliceCursorAt ikpLoopCommonPlaced
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine sepWPp_of_sepWP_lscro hregs.base.crl (mid := (blkPl_84).base + bv% (124)) ?_; wp_steps
  refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
  refine Wire.SepWPp.mono_pre
    (P' := sliceCursorAt (sp' + 32#64) ptr (b0 :: bs1) ∗
      ikpLoopCommonPlaced A sp' x.ret (b0 :: bs1).length m)
    (by unfold sliceCursorAt ikpLoopCommonPlaced; apply entails_of_eq; simp only [arm64_norm]) ?_
  exact hcont _ (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
    (hregs.of_steps hcrl1 (by simp [*, hregs.base.sp, arm64_norm])
      (by simp [*, hregs.base.trace, arm64_norm]) (by simp [*, hregs.base.x26, arm64_norm])
      (by simp [*, hregs.base.x27, arm64_norm]) (by simp [*, hregs.base.x28, arm64_norm])
      (by simp [*, hregs.x29, arm64_norm]) (by simp [*, hregs.x19, arm64_norm])
      (by simp [*, hregs.x21, arm64_norm]) (by simp [*, hregs.x24, arm64_norm]))
    (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) (by simp [*, arm64_norm])

theorem decodeLoop_124_step_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) {x : DecodeGhost} {s0 s : State} {sp' ptr : BitVec 64}
    {fuel : ℕ} {b0 : BitVec 8} {bs1 : List (BitVec 8)} {m : IdentityKeyPairStructure}
    (ih : ∀ {s : State} {ptr : BitVec 64} {bs : List (BitVec 8)} {m : IdentityKeyPairStructure},
      decodeFieldsLoop IdentityKeyPairStructure.mergeField fuel m bs =
        IdentityKeyPairStructure.decode x.bytes →
      s.pc = (blkPl_84).base + 108#64 → s.status = .Running →
      IkpLoopRegsPlaced s0 sp' x.ret s → bs.length ≤ fuel → bs.length < 2 ^ 63 →
      Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s
        (sliceCursorAt (sp' + 32#64) ptr bs ∗ ikpLoopCommonPlaced A sp' x.ret bs.length m)
        (ikpExitPostPlaced A s0 sp' x.ret ptr bs (IdentityKeyPair.tryFrom x.bytes))
        (tryFromQp s0))
    (hinv : decodeFieldsLoop IdentityKeyPairStructure.mergeField (fuel + 1) m (b0 :: bs1) =
      IdentityKeyPairStructure.decode x.bytes)
    (hpc : s.pc = (blkPl_84).base + 124#64) (hrun : s.status = .Running)
    (hregs : IkpLoopRegsPlaced s0 sp' x.ret s)
    (hx23 : s.readReg64 .x23 = sp' + 32#64) (hx22 : s.readReg64 .x22 = sp' + 40#64)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length)
    (hfuel : (b0 :: bs1).length ≤ fuel + 1) (hlen : (b0 :: bs1).length < 2 ^ 63) :
    Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s
      (sliceCursorAt (sp' + 32#64) ptr (b0 :: bs1) ∗
        ikpLoopCommonPlaced A sp' x.ret (b0 :: bs1).length m)
      (ikpExitPostPlaced A s0 sp' x.ret ptr (b0 :: bs1) (IdentityKeyPair.tryFrom x.bytes))
      (tryFromQp s0) := by
  refine decodeKey_124_placed_cps d hpc hrun hregs hx23 hx22 hx2 hlen
    (fun tag wt rest1 s1 hdk hpc1 hrun1 hregs1 hx0_1 hx1_1 => ?_)
    (fun hdk_none => by simp [IdentityKeyPair.tryFrom, ← hinv, decodeFieldsLoop, hdk_none])
  obtain ⟨k1, hk1_pos, hk1_le, hrest1_eq, htag_lt, htag_ge⟩ := decodeKey_suffix hdk
  have hrest1_len : rest1.length = (b0 :: bs1).length - k1 := by simp [hrest1_eq]
  refine ikp_advance_cursor_placed hk1_le hrest1_eq ?_
  refine Wire.SepWPp.mono_pre
    (P' := sliceCursorAt (sp' + 32#64) (ptr + BitVec.ofNat 64 k1) rest1 ∗
      ikpLoopCommonPlaced A sp' x.ret rest1.length m)
    (sepConj_mono_right (by
      unfold ikpLoopCommonPlaced
      exact sepConj_mono_right (sepConj_mono_left
        (ikpStructLoopOf_mono A (sp' + 48#64) m (by omega))))) ?_
  refine mergeField_248_placed_cps (bs := rest1) (m := m) d hpc1 hrun1 hregs1 hx0_1 hx1_1 htag_ge htag_lt (by omega)
    (fun m' rest2 s2 hmf hpc2 hrun2 hregs2 => ?_)
    (fun hmf_none => by simp [IdentityKeyPair.tryFrom, ← hinv, decodeFieldsLoop, hdk, hmf_none])
  obtain ⟨k2, hk2_le, hrest2_eq⟩ := ikp_mergeField_suffix hmf
  have hrest2_len : rest2.length = rest1.length - k2 := by simp [hrest2_eq]
  refine ikp_advance_cursor_placed hk2_le hrest2_eq ?_
  have hinv' : decodeFieldsLoop IdentityKeyPairStructure.mergeField fuel m' rest2 =
      IdentityKeyPairStructure.decode x.bytes := by
    simpa [decodeFieldsLoop, hdk, hmf] using hinv
  exact ih hinv' hpc2 hrun2 hregs2 (by omega) (by omega)

theorem decodeLoop_108_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) {x : DecodeGhost} {s0 : State} {sp' : BitVec 64}
    (hlt : x.bytes.length < 2 ^ 32) :
    ∀ (fuel : ℕ) {s : State} {ptr : BitVec 64} {bs : List (BitVec 8)} {m : IdentityKeyPairStructure},
      decodeFieldsLoop IdentityKeyPairStructure.mergeField fuel m bs =
        IdentityKeyPairStructure.decode x.bytes →
      s.pc = (blkPl_84).base + 108#64 → s.status = .Running →
      IkpLoopRegsPlaced s0 sp' x.ret s → bs.length ≤ fuel → bs.length < 2 ^ 63 →
      Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s
        (sliceCursorAt (sp' + 32#64) ptr bs ∗ ikpLoopCommonPlaced A sp' x.ret bs.length m)
        (ikpExitPostPlaced A s0 sp' x.ret ptr bs (IdentityKeyPair.tryFrom x.bytes))
        (tryFromQp s0)
  | 0, s, ptr, bs, m, hinv, hpc, hrun, hregs, hfuel, _ => by
    cases bs with
    | nil => exact loopCheck_108_empty_placed_wp d hlt hinv.symm hpc hrun hregs
    | cons b0 bs1 => simp at hfuel
  | fuel + 1, s, ptr, bs, m, hinv, hpc, hrun, hregs, hfuel, hlen => by
    cases bs with
    | nil => exact loopCheck_108_empty_placed_wp d hlt hinv.symm hpc hrun hregs
    | cons b0 bs1 =>
      refine loopCheck_108_cons_placed_cps (x := x) hpc hrun hregs hlen ?_
      intro s1 hpc1 hrun1 hregs1 hx23_1 hx22_1 hx2_1
      exact decodeLoop_124_step_placed_wp d (decodeLoop_108_placed_wp d hlt fuel)
        hinv hpc1 hrun1 hregs1 hx23_1 hx22_1 hx2_1 hfuel hlen

theorem ikp_entry_to_812_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) {x : DecodeGhost} {s0 : State}
    (hlt : x.bytes.length < 2 ^ 32)
    (hpc : s0.pc = (blkPl_84).base) (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = x.bytesA)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length)
    (hx8 : s0.readReg64 .x8 = x.ret) :
    Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s0
      (memRegion (s0.sp - 224#64) 144 ∗ memRegion (s0.sp - 224#64 + 144#64) 80 ∗
        memRegion x.ret 72 ∗ (x.bytesA ↦ₛ x.bytes) ∗ lsLogOff ∗ A.pool ∗
        stackAt (s0.sp - 224#64) (skipFieldStackX 100))
      (fun sf Pf => IkpBaseStatePlaced s0 (s0.sp - 224#64) sf ∧
        (Pf ⊢ memRegion (s0.sp - 224#64) 144 ∗
          ((s0.sp - 224#64 + 168#64) ↦₆₄ (s0.sp - 224#64 + 32#64)) ∗
          ikpCalleeSavedAt (s0.sp - 224#64) s0 ∗
          identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes) ∗ lsLogOff ∗ A.pool ∗
          stackAt (s0.sp - 224#64) (skipFieldStackX 100)))
      (tryFromQp s0) := by
  have hpost := @post_344_placed_wp _ A H d x s0
  have hstep := @decodeLoop_124_step_placed_wp _ A H d x s0
  have hloop := decodeLoop_108_placed_wp (A := A) (H := H) (x := x) (s0 := s0) (sp' := s0.sp - 224#64) d hlt
  refine Wire.SepWPp.mono_pre
    (sepConj_mono (ikpMem144_prologue_cells (s0.sp - 224#64))
      (sepConj_mono_left (ikpMem80_cells (s0.sp - 224#64)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun w88 => Wire.SepWPp.exists_pre fun w80 =>
    Wire.SepWPp.exists_pre fun w72 => Wire.SepWPp.exists_pre fun w64 =>
    Wire.SepWPp.exists_pre fun w56 => Wire.SepWPp.exists_pre fun w48 =>
    Wire.SepWPp.exists_pre fun w40 => Wire.SepWPp.exists_pre fun w32 =>
    Wire.SepWPp.exists_pre fun c19 => Wire.SepWPp.exists_pre fun c20 =>
    Wire.SepWPp.exists_pre fun c21 => Wire.SepWPp.exists_pre fun c22 =>
    Wire.SepWPp.exists_pre fun c23 => Wire.SepWPp.exists_pre fun c24 =>
    Wire.SepWPp.exists_pre fun cbuf => Wire.SepWPp.exists_pre fun c25 =>
    Wire.SepWPp.exists_pre fun c30 => Wire.SepWPp.exists_pre fun c29 => ?_
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
  have _hsp224_b : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub224 hsp
  have _hsp224 : (s0.sp - 224#64) &&& 15#64 = 0#64 := eq_of_beq _hsp224_b
  rcases hbs : x.bytes with _ | ⟨b0, bs1⟩
  · have hx1_0 : s0.readReg64 .x1 = 0#64 := by simp [hx1, hbs]
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_84).base + bv% (344)) ?_; wp_steps
    refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
    have hdec0 : IdentityKeyPairStructure.decode x.bytes = some IdentityKeyPairStructure.empty := by
      simp [hbs, IdentityKeyPairStructure.decode, decodeFieldsLoop]
    have hbase1 : IkpBaseStatePlaced s0 (s0.sp - 224#64) _ := {
      sp := by simp [*, arm64_norm]
      spAligned := by rw [State.spAligned]; simpa [arm64_norm] using spAligned_sub224 hsp
      crl := hcrl1
      trace := by simp [*, arm64_norm]
      x26 := by simp [*, arm64_norm]
      x27 := by simp [*, arm64_norm]
      x28 := by simp [*, arm64_norm]
    }
    have hm16 := pointsTo64_pair_entails_memRegion16 (s0.sp - 224#64 + 32#64) x.bytesA 0#64
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm16
    have h144 := ikpFold144 (s0.sp - 224#64) 0#64 1#64 0#64 0#64 1#64 0#64
    dsimp only [vecHeader] at h144; simp only [BitVec.add_assoc, BitVec.reduceAdd] at h144
    refine Wire.SepWPp.mono_pre
      (P' := (memRegion (s0.sp - 224#64) 32 ∗ memRegion (s0.sp - 224#64 + 96#64) 48 ∗
        memRegion x.ret 72 ∗
        vecU8Buf A 0#64 1#64 IdentityKeyPairStructure.empty.publicKey ∗
        vecU8Buf A 0#64 1#64 IdentityKeyPairStructure.empty.privateKey ∗
        lsLogOff ∗ A.pool ∗ stackAt (s0.sp - 224#64) (skipFieldStackX 100)) ∗
        (memRegion (s0.sp - 224#64 + 32#64) 16 ∗
          ((s0.sp - 224#64 + 48#64) ↦₆₄ 0#64) ∗ ((s0.sp - 224#64 + 56#64) ↦₆₄ 1#64) ∗
          ((s0.sp - 224#64 + 64#64) ↦₆₄ 0#64) ∗
          ((s0.sp - 224#64 + 72#64) ↦₆₄ 0#64) ∗ ((s0.sp - 224#64 + 80#64) ↦₆₄ 1#64) ∗
          ((s0.sp - 224#64 + 88#64) ↦₆₄ 0#64) ∗
          ((s0.sp - 224#64 + 168#64) ↦₆₄ (s0.sp - 224#64 + 32#64)) ∗
          ikpCalleeSavedAt (s0.sp - 224#64) s0 ∗ (x.bytesA ↦ₛ x.bytes)))
      (by dsimp only [IdentityKeyPairStructure.empty]
          have hemp0 : (⌜([] : List (BitVec 8)) = []⌝ : SepProp) = emp := pure_true_emp rfl
          try simp only [vecU8Buf_zero]
          try simp only [hemp0]
          try simp only [emp_sepConj]
          refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_left hm16))
          unfold ikpCalleeSavedAt
          dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x29, Reg.x30]
          try rw [hbs]; apply entails_of_eq
          try dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x29, Reg.x30]
          try simp only [BitVec.add_assoc]
          try simp only [BitVec.reduceAdd]
          try simp only [bv_sub_add_lit]
          try simp only [BitVec.add_assoc]
          try simp only [BitVec.reduceAdd]
          try simp only [bv_sub_add_lit]
          try simp only [arm64_norm]
          ac_rfl) ?_
    refine Wire.SepWPp.frame_tryFrom
      (Q' := fun sf Pf => IkpBaseStatePlaced s0 (s0.sp - 224#64) sf ∧
        (Pf ⊢ memRegion (s0.sp - 224#64) 32 ∗ memRegion (s0.sp - 224#64 + 96#64) 48 ∗
          identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
          lsLogOff ∗ A.pool ∗ stackAt (s0.sp - 224#64) (skipFieldStackX 100)))
      (hpost hdec0 (by decide) (by decide) hbase1
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (by simp [*, speWord, arm64_norm]) (by simp [*, IdentityKeyPairStructure.empty, arm64_norm])
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (by simp [*, IdentityKeyPairStructure.empty, arm64_norm]))
      fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hentf) ?_
    refine Entails.trans ?_ (sepConj_mono_left h144)
    rw [hbs]; apply entails_of_eq
    try dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x29, Reg.x30]
    try simp only [BitVec.add_assoc]
    try simp only [BitVec.reduceAdd]
    try simp only [bv_sub_add_lit]
    try simp only [BitVec.add_assoc]
    try simp only [BitVec.reduceAdd]
    try simp only [bv_sub_add_lit]
    try simp only [arm64_norm]
    ac_rfl
  · have hlen63 : (b0 :: bs1).length < 2 ^ 63 := by rw [← hbs]; omega
    obtain ⟨hc_eq, hc_ne⟩ := cons_len_bv64_ne_zero b0 bs1 hlen63
    have hx1_cons : s0.readReg64 .x1 = BitVec.ofNat 64 (b0 :: bs1).length := by simpa [hbs] using hx1
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_84).base + bv% (124)) ?_; wp_steps
    refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
    have hregs1 : IkpLoopRegsPlaced s0 (s0.sp - 224#64) x.ret _ := {
      base := {
        sp := by simp [*, arm64_norm]
        spAligned := by rw [State.spAligned]; simpa [arm64_norm] using spAligned_sub224 hsp
        crl := hcrl1
        trace := by simp [*, arm64_norm]
        x26 := by simp [*, arm64_norm]
        x27 := by simp [*, arm64_norm]
        x28 := by simp [*, arm64_norm]
      }
      x29 := by simp [*, arm64_norm]
      x19 := by simp [*, arm64_norm]
      x21 := by simp [*, arm64_norm]
      x24 := by simp [*, speWord, arm64_norm]
    }
    have hemptyLoop :
        ((s0.sp - 224#64 + 48#64) ↦₆₄ 0#64) ∗ ((s0.sp - 224#64 + 56#64) ↦₆₄ 1#64) ∗
          ((s0.sp - 224#64 + 64#64) ↦₆₄ 0#64) ∗
          ((s0.sp - 224#64 + 72#64) ↦₆₄ 0#64) ∗ ((s0.sp - 224#64 + 80#64) ↦₆₄ 1#64) ∗
          ((s0.sp - 224#64 + 88#64) ↦₆₄ 0#64) ⊢
          ikpStructLoopOf A (s0.sp - 224#64 + 48#64) (b0 :: bs1).length
            IdentityKeyPairStructure.empty :=
      Entails.trans (ikpEmptyCells_entails_structAt A (s0.sp - 224#64))
        (ikpStructAt_entails_loopOf A ⟨0#64, 1#64⟩ ⟨0#64, 1#64⟩
          (s0.sp - 224#64 + 48#64) (b0 :: bs1).length IdentityKeyPairStructure.empty
          bytesMergeCapOk_zero bytesMergeCapOk_zero)
    have hinv0 : decodeFieldsLoop IdentityKeyPairStructure.mergeField
        (bs1.length + 1) IdentityKeyPairStructure.empty (b0 :: bs1) =
        IdentityKeyPairStructure.decode x.bytes := by
      simp [hbs, IdentityKeyPairStructure.decode]
    refine Wire.SepWPp.mono_pre
      (P' := (sliceCursorAt (s0.sp - 224#64 + 32#64) x.bytesA (b0 :: bs1) ∗
        ikpLoopCommonPlaced A (s0.sp - 224#64) x.ret (b0 :: bs1).length
          IdentityKeyPairStructure.empty) ∗
        ikpCalleeSavedAt (s0.sp - 224#64) s0)
      (by unfold sliceCursorAt ikpLoopCommonPlaced ikpCalleeSavedAt
          dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x29, Reg.x30]
          refine Entails.trans ?_
            (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hemptyLoop))))
          apply entails_of_eq
          try dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x29, Reg.x30]
          try simp only [BitVec.add_assoc]
          try simp only [BitVec.reduceAdd]
          try simp only [bv_sub_add_lit]
          try simp only [BitVec.add_assoc]
          try simp only [BitVec.reduceAdd]
          try simp only [bv_sub_add_lit]
          try simp only [arm64_norm]
          ac_rfl) ?_
    refine Wire.SepWPp.frame_tryFrom
      (Q' := ikpExitPostPlaced A s0 (s0.sp - 224#64) x.ret x.bytesA (b0 :: bs1)
        (IdentityKeyPair.tryFrom x.bytes))
      (hstep (hloop bs1.length) hinv0 (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        hregs1 (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (by simp [*, arm64_norm]) (Nat.le_refl _) hlen63)
      fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
    unfold ikpExitMemPlaced at hentf
    refine Entails.trans (sepConj_mono_left hentf) ?_; apply entails_of_eq
    try dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x29, Reg.x30]
    try simp only [BitVec.add_assoc]
    try simp only [BitVec.reduceAdd]
    try simp only [bv_sub_add_lit]
    try simp only [BitVec.add_assoc]
    try simp only [BitVec.reduceAdd]
    try simp only [bv_sub_add_lit]
    try simp only [arm64_norm]
    rw [hbs]; ac_rfl

theorem ikp_placed_subroutine_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) :
    subroutine_ok (lsProg_84 H) (blkPl_84).base (identityKeyPairTryFromPlacedSpec A) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp hL => ?_
  have ⟨hcrl, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [identityKeyPairTryFromRawSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1_nat, hlt, hx8⟩, hmem⟩
  have hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length := by
    rw [← hx1_nat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hmem' : s0.mem ⊨
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 72 ∗ lsLogOff ∗
        stackAt s0.sp smallRootStack ∗ A.pool) ∗ R := by
    ac_nf at hmem ⊢
  have h1 : Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s0
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 72 ∗ lsLogOff ∗
        stackAt s0.sp smallRootStack ∗ A.pool)
      (fun sm Pm =>
        IkpBaseStatePlaced s0 (s0.sp - 224#64) sm ∧
        (Pm ⊢ memRegion (s0.sp - 224#64 - BitVec.ofNat 64 ikpSubStack)
            (ikpSubStack - skipFieldStackX 100) ∗
          stackAt (s0.sp - 224#64) (skipFieldStackX 100) ∗
          memRegion (s0.sp - 224#64) 144 ∗
          ((s0.sp - 224#64 + 168#64) ↦₆₄ (s0.sp - 224#64 + 32#64)) ∗
          ikpCalleeSavedAt (s0.sp - 224#64) s0 ∗
          identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes) ∗ lsLogOff ∗ A.pool))
      (tryFromQp s0) := by
    refine Wire.SepWPp.mono_pre
      (P' := (memRegion (s0.sp - 224#64) 144 ∗ memRegion (s0.sp - 224#64 + 144#64) 80 ∗
        memRegion x.ret 72 ∗ (x.bytesA ↦ₛ x.bytes) ∗ lsLogOff ∗ A.pool ∗
        stackAt (s0.sp - 224#64) (skipFieldStackX 100)) ∗
        memRegion (s0.sp - 224#64 - BitVec.ofNat 64 ikpSubStack) (ikpSubStack - skipFieldStackX 100))
      (by rw [ikpRootStack_split s0.sp]; apply entails_of_eq
          try dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x29, Reg.x30]
          try simp only [BitVec.add_assoc]
          try simp only [BitVec.reduceAdd]
          try simp only [bv_sub_add_lit]
          try simp only [BitVec.add_assoc]
          try simp only [BitVec.reduceAdd]
          try simp only [bv_sub_add_lit]
          try simp only [arm64_norm]
          ac_rfl) ?_
    refine Wire.SepWPp.frame_tryFrom
      (ikp_entry_to_812_placed_wp d hlt hpc hrun hsp hcrl hx0 hx1 hx8)
      fun sm Pm ⟨hstm, hentm⟩ => ⟨hstm, ?_⟩
    refine Entails.trans (sepConj_mono_left hentm) ?_; apply entails_of_eq
    try dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x29, Reg.x30]
    try simp only [BitVec.add_assoc]
    try simp only [BitVec.reduceAdd]
    try simp only [bv_sub_add_lit]
    try simp only [BitVec.add_assoc]
    try simp only [BitVec.reduceAdd]
    try simp only [bv_sub_add_lit]
    try simp only [arm64_norm]
    ac_rfl
  have hfull : Wire.SepWPp (lsProg_84 H) (s0.readReg64 .x30) s0
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 72 ∗ lsLogOff ∗
        stackAt s0.sp smallRootStack ∗ A.pool)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        (Pf ⊢ (identityKeyPairTryFromPlacedSpec A).post x s0 sf))
      (tryFromQp s0) := by
    refine Wire.SepWPp.bind h1 ?_
    intro sm Pm hpcm hrunm ⟨hstm, hentm⟩
    exact Wire.SepWPp.mono_pre hentm
      (epilogue_812_placed_wp (A := A) (H := H) (x := x)
        (wbuf := s0.sp - 224#64 + 32#64) hstm hpcm hrunm)
  obtain ⟨sf, hsteps, hex⟩ := hfull R hmem' hL
  refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
  rcases hex with ⟨hpc_f, hrun_f, Pf, hmf, ⟨hsp_f, hcs_f, hent_f⟩, hv_f⟩ |
    ⟨hpan, Pf, hmf, htr_f⟩ | ⟨_, hoom⟩
  · exact Or.inl ⟨⟨hpc_f, hsp_f, hrun_f⟩, ⟨hsp_f, hcs_f hv_f⟩,
      Satisfies.mono (sepConj_mono_left hent_f) hmf⟩
  · exact Or.inr (Or.inl ⟨hpan, htr_f R hmf⟩)
  · exact (allowPanic_not_exited hoom).elim

end Placed

end CryptoVerification.RecordCodecsBinary.IdentityKeyPairTryFrom.Helpers

namespace CryptoVerification.RecordCodecsBinary.IdentityKeyPairTryFrom

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.RecordCodecs.Placed

/-- `<IdentityKeyPair as TryFrom<&[u8]>>::try_from` meets `identityKeyPairTryFromPlacedSpec`
under any `[LibsignalPlacement]`, given `PortDepsPlaced A H`. -/
theorem identityKeyPair_tryFrom_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) :
    subroutine_ok (lsProg_84 H) (blkPl_84).base (identityKeyPairTryFromPlacedSpec A) :=
  Helpers.ikp_placed_subroutine_ok d

end CryptoVerification.RecordCodecsBinary.IdentityKeyPairTryFrom
