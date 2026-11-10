/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.Decode
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import ProofLib.SepLogic.WPp

/-!
# `IdentityKeyPair::try_from` Convergence Invariant and Error Cleanup

Convergence invariant at `+812`, scratch/frame folding helpers, and the `DecodeError` cleanup tail
(`+616 .. +684` → `+812`) for `<IdentityKeyPair as TryFrom<&[u8]>>::try_from`.
-/

@[expose] public section

set_option autoImplicit false

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

section LoopHelpersStateSimp

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_lh (s : State) (pc : BitVec 64) : (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_lh (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPState_lh (s : State) (ps : PState) : (s.setPState ps).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_advancePC_lh (s : State) : s.advancePC.sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_writeReg64_gpr_lh (s : State) (idx : BitVec 5) (val : BitVec 64) :
    (s.writeReg64 (Reg.gpr idx) val).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_writeReg32_gpr_lh (s : State) (idx : BitVec 5) (val : BitVec 32) :
    (s.writeReg32 (Reg.gpr idx) val).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_writeReg_gpr_lh (s : State) (w : Width) (idx : BitVec 5) (val : BitVec 64) :
    (s.writeReg w (Reg.gpr idx) val).sp = s.sp := by cases w <;> cases s <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_lh (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_lh (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPState_lh (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg64 r = s.readReg64 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_lh (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_lh (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPState_lh (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg32 r = s.readReg32 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_lh (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_lh (s : State) (m : Memory) (w : RegWidth) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPState_lh (s : State) (ps : PState) (w : RegWidth) (r : Reg) :
    (s.setPState ps).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

end LoopHelpersStateSimp

/-! ## Single convergence invariant at `+812` & cursor advancement -/

def ikpExitMem (img : Obj.Image) (A : RustAlloc) (sp' ret ptr : BitVec 64)
    (bs : List (BitVec 8)) (out : Except SignalProtocolError IdentityKeyPair) : SepProp :=
  memRegion sp' 144 ∗
    ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗
    identityKeyPairResultAt A ret out ∗
    (ptr ↦ₛ bs) ∗
    logOff img ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100)

def ikpExitPost (img : Obj.Image) (A : RustAlloc) (s0 : State)
    (sp' ret ptr : BitVec 64) (bs : List (BitVec 8))
    (out : Except SignalProtocolError IdentityKeyPair)
    (sf : State) (Pf : SepProp) : Prop :=
  IkpBaseState img s0 sp' sf ∧ (Pf ⊢ ikpExitMem img A sp' ret ptr bs out)

theorem IkpLoopRegs.of_steps {img : Obj.Image} {s0 s1 s2 : State} {sp' ret : BitVec 64}
    (hr : IkpLoopRegs img s0 sp' ret s1)
    (hF : img.FrozenLoaded s2) (hsym : s2.symtab = img.symtab)
    (hsp : s2.sp = sp') (htr : s2.trace = s0.trace)
    (h26 : s2.readReg64 .x26 = s0.readReg64 .x26)
    (h27 : s2.readReg64 .x27 = s0.readReg64 .x27)
    (h28 : s2.readReg64 .x28 = s0.readReg64 .x28)
    (h29 : s2.readReg64 .x29 = sp' + 144#64)
    (h19 : s2.readReg64 .x19 = ret)
    (h21 : s2.readReg64 .x21 = sp' + 48#64)
    (h24 : s2.readReg64 .x24 = speWord 9) :
    IkpLoopRegs img s0 sp' ret s2 where
  base := hr.base.of_steps hF hsym hsp htr h26 h27 h28
  x29 := h29
  x19 := h19
  x21 := h21
  x24 := h24

theorem pointsToBytes_take_drop :
    ∀ (k : Nat) (bs : List (BitVec 8)) (ptr : BitVec 64),
      k ≤ bs.length →
      (ptr ↦ₛ bs) =
        (ptr ↦ₛ bs.take k) ∗ ((ptr + BitVec.ofNat 64 k) ↦ₛ bs.drop k)
  | 0, bs, ptr, _ => by
    simp [pointsToBytes_nil, BitVec.ofNat]
  | k + 1, [], _, hk => by simp at hk
  | k + 1, b :: bs, ptr, hk => by
    rw [List.take_succ_cons, List.drop_succ_cons,
      pointsToBytes_cons ptr b bs,
      pointsToBytes_cons ptr b (bs.take k),
      pointsToBytes_take_drop k bs (ptr + 1#64) (by simp at hk; omega)]
    have ha : ptr + 1#64 + BitVec.ofNat 64 k = ptr + BitVec.ofNat 64 (k + 1) := by
      rw [BitVec.ofNat_add k 1]; bv_omega
    rw [ha, sepConj_assoc]

theorem ikp_advance_cursor {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {s0 s : State} {sp' ret ptr : BitVec 64}
    {bs rest : List (BitVec 8)} {k : Nat}
    {R : SepProp} {out : Except SignalProtocolError IdentityKeyPair}
    (hkl : k ≤ bs.length) (hrest : rest = bs.drop k)
    (hsub : Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s
      (sliceCursorAt (sp' + 32#64) (ptr + BitVec.ofNat 64 k) rest ∗ R)
      (ikpExitPost img A s0 sp' ret (ptr + BitVec.ofNat 64 k) rest out)
      (tryFromQp s0)) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s
      (sliceCursorAfter (sp' + 32#64) ptr bs rest ∗ R)
      (ikpExitPost img A s0 sp' ret ptr bs out)
      (tryFromQp s0) := by
  have hk_eq : bs.length - rest.length = k := by
    rw [hrest, List.length_drop]; omega
  have hsplit := pointsToBytes_take_drop k bs ptr hkl
  rw [← hrest] at hsplit
  refine Wire.SepWPp.mono_pre
    (P' := (sliceCursorAt (sp' + 32#64) (ptr + BitVec.ofNat 64 k) rest ∗ R) ∗ (ptr ↦ₛ bs.take k))
    (by
      unfold sliceCursorAfter sliceCursorAt
      rw [hk_eq, hsplit]
      apply entails_of_eq; ac_rfl) ?_
  refine Wire.SepWPp.frame_tryFrom
    (Q' := ikpExitPost img A s0 sp' ret (ptr + BitVec.ofNat 64 k) rest out)
    hsub
    fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
  refine Entails.trans (sepConj_mono_left hentf) ?_
  unfold ikpExitMem
  rw [hsplit]
  apply entails_of_eq; ac_rfl

/-! ## Scratch (`sp' + 96 .. sp' + 144`) and frame (`sp' .. sp' + 144`) folding helpers -/

theorem ikpMem48_split24 (sp' : BitVec 64) :
    memRegion (sp' + 96#64) 48 =
      memRegion (sp' + 96#64) 24 ∗ memRegion (sp' + 120#64) 24 := by
  have hs := Prost.memRegion_split (sp' + 96#64) 24 24 (by decide)
  have ha : sp' + 96#64 + 24#64 = sp' + 120#64 := by bv_omega
  rw [ha] at hs; exact hs

theorem ikpMem48_split8 (sp' : BitVec 64) :
    memRegion (sp' + 96#64) 48 =
      memRegion (sp' + 96#64) 8 ∗ memRegion (sp' + 104#64) 40 := by
  have hs := Prost.memRegion_split (sp' + 96#64) 8 40 (by decide)
  have ha : sp' + 96#64 + 8#64 = sp' + 104#64 := by bv_omega
  rw [ha] at hs; exact hs

theorem ikpMem48_split_96_104_112 (sp' : BitVec 64) :
    memRegion (sp' + 96#64) 48 =
      (∃∗ w0 : BitVec 64, (sp' + 96#64) ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (sp' + 104#64) ↦₆₄ w1) ∗
      memRegion (sp' + 112#64) 32 := by
  rw [Prost.memRegion_split (sp' + 96#64) 8 40 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 8#64) 8 32 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  have ha1 : sp' + 96#64 + 8#64 = sp' + 104#64 := by bv_omega
  have ha2 : sp' + 104#64 + 8#64 = sp' + 112#64 := by bv_omega
  rw [ha1, ha2]

theorem ikpPointsTo64_104_mem32_entails_mem40 (sp' v : BitVec 64) :
    ((sp' + 104#64) ↦₆₄ v) ∗ memRegion (sp' + 112#64) 32 ⊢ memRegion (sp' + 104#64) 40 := by
  rw [Prost.memRegion_split (sp' + 104#64) 8 32 (by decide)]
  have ha : sp' + 104#64 + 8#64 = sp' + 112#64 := by bv_omega
  rw [ha]
  exact sepConj_mono_left (pointsTo64_entails_memRegion (sp' + 104#64) v)

theorem ikpPointsTo64_96_mem40_entails_mem48 (sp' v : BitVec 64) :
    ((sp' + 96#64) ↦₆₄ v) ∗ memRegion (sp' + 104#64) 40 ⊢ memRegion (sp' + 96#64) 48 := by
  rw [ikpMem48_split8 sp']
  exact sepConj_mono_left (pointsTo64_entails_memRegion (sp' + 96#64) v)

theorem ikpScratch24_ok_entails_mem48 (sp' v w : BitVec 64) :
    ((sp' + 96#64) ↦₃₂ 0#32) ∗ ((sp' + 100#64) ↦₃₂ 0#32) ∗
      ((sp' + 104#64) ↦₆₄ v) ∗ ((sp' + 112#64) ↦₆₄ w) ∗
      memRegion (sp' + 120#64) 24 ⊢
      memRegion (sp' + 96#64) 48 := by
  have h0 : ((sp' + 96#64) ↦₃₂ 0#32) ∗ ((sp' + 100#64) ↦₃₂ 0#32) =
      ((sp' + 96#64) ↦₆₄ 0#64) := by
    have hs := (pointsTo64_zero_split32 (sp' + 96#64)).symm
    have ha : sp' + 96#64 + 4#64 = sp' + 100#64 := by bv_omega
    rw [ha] at hs; exact hs
  rw [← sepConj_assoc, h0, ikpMem48_split24 sp',
    Prost.memRegion_split (sp' + 96#64) 8 16 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 8#64) 8 8 (by decide)]
  have ha1 : sp' + 96#64 + 8#64 = sp' + 104#64 := by bv_omega
  have ha2 : sp' + 104#64 + 8#64 = sp' + 112#64 := by bv_omega
  rw [ha1, ha2]
  refine Entails.trans ?_
    (sepConj_mono
      (sepConj_mono (pointsTo64_entails_memRegion (sp' + 96#64) 0#64)
        (sepConj_mono (pointsTo64_entails_memRegion (sp' + 104#64) v)
          (pointsTo64_entails_memRegion (sp' + 112#64) w)))
      (Entails.refl _))
  apply entails_of_eq; ac_rfl

theorem ikpScratch24_err_entails_mem48 (sp' e : BitVec 64) :
    ((sp' + 96#64) ↦₃₂ 1#32) ∗ ((sp' + 100#64) ↦₃₂ 0#32) ∗
      ((sp' + 104#64) ↦₆₄ e) ∗ memRegion (sp' + 112#64) 8 ∗
      memRegion (sp' + 120#64) 24 ⊢
      memRegion (sp' + 96#64) 48 := by
  have h1 : ((sp' + 96#64) ↦₃₂ 1#32) ∗ ((sp' + 100#64) ↦₃₂ 0#32) =
      ((sp' + 96#64) ↦₆₄ 1#64) := by
    have hs := (pointsTo64_one_split32 (sp' + 96#64)).symm
    have ha : sp' + 96#64 + 4#64 = sp' + 100#64 := by bv_omega
    rw [ha] at hs; exact hs
  rw [← sepConj_assoc, h1, ikpMem48_split24 sp',
    Prost.memRegion_split (sp' + 96#64) 8 16 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 8#64) 8 8 (by decide)]
  have ha1 : sp' + 96#64 + 8#64 = sp' + 104#64 := by bv_omega
  have ha2 : sp' + 104#64 + 8#64 = sp' + 112#64 := by bv_omega
  rw [ha1, ha2]
  refine Entails.trans ?_
    (sepConj_mono
      (sepConj_mono (pointsTo64_entails_memRegion (sp' + 96#64) 1#64)
        (sepConj_mono (pointsTo64_entails_memRegion (sp' + 104#64) e)
          (Entails.refl _)))
      (Entails.refl _))
  apply entails_of_eq; ac_rfl

theorem vecHeader_entails_memRegion24 (a cap ptr len : BitVec 64) :
    vecHeader a cap ptr len ⊢ memRegion a 24 := by
  unfold vecHeader
  rw [Prost.memRegion_split a 8 16 (by decide),
    Prost.memRegion_split (a + 8#64) 8 8 (by decide)]
  have ha : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  rw [ha]
  exact sepConj_mono (pointsTo64_entails_memRegion a cap)
    (sepConj_mono (pointsTo64_entails_memRegion (a + 8#64) ptr)
      (pointsTo64_entails_memRegion (a + 16#64) len))

theorem vecU8At_eq_header_buf (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A a cap ptr bs = vecHeader a cap ptr (BitVec.ofNat 64 bs.length) ∗ vecU8Buf A cap ptr bs :=
  rfl

theorem ikpFold144 (sp' pkCap pkPtr pkLen skCap skPtr skLen : BitVec 64) :
    memRegion sp' 32 ∗
      memRegion (sp' + 32#64) 16 ∗
      vecHeader (sp' + 48#64) pkCap pkPtr pkLen ∗
      vecHeader (sp' + 72#64) skCap skPtr skLen ∗
      memRegion (sp' + 96#64) 48 ⊢
      memRegion sp' 144 := by
  rw [Prost.memRegion_split sp' 32 112 (by decide),
    Prost.memRegion_split (sp' + 32#64) 16 96 (by decide),
    Prost.memRegion_split (sp' + 32#64 + 16#64) 24 72 (by decide),
    Prost.memRegion_split (sp' + 32#64 + 16#64 + 24#64) 24 48 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (Entails.refl _)
    (sepConj_mono (Entails.refl _)
      (sepConj_mono (vecHeader_entails_memRegion24 (sp' + 48#64) pkCap pkPtr pkLen)
        (sepConj_mono (vecHeader_entails_memRegion24 (sp' + 72#64) skCap skPtr skLen)
          (Entails.refl _))))

/-! ## DecodeError cleanup tail (`+616 .. +684` → `+812`) & `DecodeError::from` / `push` -/

theorem decodeErr_660_wp {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (d : DecodeDeps img A ext)
    {x : DecodeGhost} {s0 s : State} {sp' errPtr : BitVec 64}
    (htry_err : IdentityKeyPair.tryFrom x.bytes = .error .invalidProtobufEncoding)
    (hst : IkpBaseState img s0 sp' s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 660#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx24 : s.readReg64 .x24 = speWord 9)
    (hx20 : s.readReg64 .x20 = errPtr) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s
      (memRegion x.ret 72 ∗ decodeErrorAt A errPtr ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => IkpBaseState img s0 sp' sf ∧
        (Pf ⊢ identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  let H := Rust.withPanics ext
  have hcall := ikp_dropDecodeError_ok d
  refine Wire.SepWPp.mono_pre
    (sepConj_mono_left (memRegion72_split_err x.ret)) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun w2 => Wire.SepWPp.exists_pre fun w1 =>
    Wire.SepWPp.exists_pre fun b0 => ?_
  code_fetches_from CryptoVerification.libsignalSessionCode
    ikpTryFromBin img.base H
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
    (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))
    660 28
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr identityKeyPairTryFromName = entry
  examples_hide_fetches
  have hsp_subst := hst.sp
  subst hsp_subst
  have hstack := stackAt_sub_split s.sp dropDecodeErrorStackX (skipFieldStackX 100)
  refine Wire.SepWPp.of_sepWP_frozen hst.frozen hst.symtab
    (mid := entry + bv% (2 ^ 64 +
      (ls_off% "core::ptr::drop_glue::<prost::error::DecodeError> [local#1]") -
      (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))) ?_
  wp_steps
  refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hF1 hsym1
  refine Wire.SepWPp.call_noPanic_tryFrom errPtr hcall
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by tryFromPost_sp_align hst.spAligned) hF1 hsym1
    (ret_pc := entry + bv% (668)) (by simp_all [arm64_norm])
    (T := decodeErrorAt A errPtr ∗ A.pool ∗ stackAt s.sp dropDecodeErrorStackX)
    (φ := errPtr = errPtr)
    (by simp_all [dropDecodeErrorSpecX, arm64_norm])
    rfl
    (by rw [hstack]; sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  dsimp only [dropDecodeErrorSpecX]
  rw [sepConj_assoc]
  refine Wire.SepWPp.pure_pre fun htr2 => ?_
  have hx19_2 : s2.readReg64 .x19 = x.ret := hcs2.1.trans (by simp_all [arm64_norm])
  have hx24_2 : s2.readReg64 .x24 = speWord 9 := hcs2.2.2.2.2.2.1.trans (by simp_all [arm64_norm])
  refine Wire.SepWPp.of_sepWP_end hF2 hsym2 ?_
  wp_steps
  refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hF3 hsym3
  have hst1 := hst.of_steps hF1 hsym1 rfl
    (by simp_all [hst.trace, arm64_norm])
    (by simp_all [hst.x26, arm64_norm])
    (by simp_all [hst.x27, arm64_norm])
    (by simp_all [hst.x28, arm64_norm])
  have hst2 := hst1.of_calleeSaved hsp2 hsp2_align hF2 hsym2 (htr2.trans hst1.trace) hcs2
  refine ⟨hst2.of_steps hF3 hsym3
    (by simp_all [hst2.sp, arm64_norm])
    (by simp_all [hst2.trace, arm64_norm])
    (by simp_all [hst2.x26, arm64_norm])
    (by simp_all [hst2.x27, arm64_norm])
    (by simp_all [hst2.x28, arm64_norm]), ?_⟩
  have hspe : speWord 9 - 7#64 = speWord 2 := rfl
  have hres := ikpResult_err_spe2 A x.ret w2 htry_err
  simp only [arm64_norm, hspe]
  refine Entails.trans ?_
    (sepConj_mono hres (Entails.refl _))
  apply entails_of_eq
  rw [hstack]
  ac_rfl

theorem decodeErr_640_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsX img C A encFn decFn ext)
    (d : DecodeDeps img A ext)
    {x : DecodeGhost} {s0 s : State} {sp' skCap skPtr errPtr : BitVec 64}
    {skBs : List (BitVec 8)}
    (htry_err : IdentityKeyPair.tryFrom x.bytes = .error .invalidProtobufEncoding)
    (hst : IkpBaseState img s0 sp' s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 640#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx24 : s.readReg64 .x24 = speWord 9)
    (hx20 : s.readReg64 .x20 = errPtr)
    (hx21 : s.readReg64 .x21 = skCap)
    (hx22 : s.readReg64 .x22 = skPtr) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s
      (vecU8Buf A skCap skPtr skBs ∗ memRegion x.ret 72 ∗
        decodeErrorAt A errPtr ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => IkpBaseState img s0 sp' sf ∧
        (Pf ⊢ identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  let H := Rust.withPanics ext
  have hnext := @decodeErr_660_wp img A ext d x s0
  by_cases hcap : skCap = 0#64
  · subst hcap
    rw [vecU8Buf_zero]
    refine Wire.SepWPp.pure_pre fun _ => ?_
    code_fetches_from CryptoVerification.libsignalSessionCode
      ikpTryFromBin img.base H
      (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
      (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))
      640 4
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr identityKeyPairTryFromName = entry
    examples_hide_fetches
    have _hsp_eq := hst.sp
    refine Wire.SepWPp.of_sepWP_frozen hst.frozen hst.symtab (mid := entry + bv% (660)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    intro hF1 hsym1
    exact hnext htry_err
      (hst.of_steps hF1 hsym1 (by simp_all [arm64_norm])
        (by simp_all [hst.trace, arm64_norm])
        (by simp_all [hst.x26, arm64_norm])
        (by simp_all [hst.x27, arm64_norm])
        (by simp_all [hst.x28, arm64_norm]))
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm])
  · refine Wire.SepWPp.mono_pre
      (sepConj_mono_left (vecU8Buf_dealloc A skCap skPtr skBs hcap)) ?_
    simp only [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hcall := ikp_dealloc_ok hC
    code_fetches_from CryptoVerification.libsignalSessionCode
      ikpTryFromBin img.base H
      (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
      (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))
      640 20
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr identityKeyPairTryFromName = entry
    examples_hide_fetches
    have hsp_subst := hst.sp
    subst hsp_subst
    have hstack := stackAt_sub_split s.sp extHookStack (skipFieldStackX 100)
    have _hne : (skCap == 0#64) = false := beq_false_of_ne hcap
    refine Wire.SepWPp.of_sepWP_frozen hst.frozen hst.symtab
      (mid := entry + bv% ((ls_off% "__rustc::__rust_dealloc") -
        (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))) ?_
    wp_steps
    refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    intro hF1 hsym1
    refine Wire.SepWPp.call_noPanic_tryFrom (skPtr, skCap.toNat, 1) hcall
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by tryFromPost_sp_align hst.spAligned) hF1 hsym1
      (ret_pc := entry + bv% (660)) (by simp_all [arm64_norm])
      (T := A.pool ∗ A.live skPtr skCap.toNat 1 ∗ memRegion skPtr skCap.toNat ∗ stackAt s.sp extHookStack)
      (φ := skPtr = skPtr ∧ skCap.toNat = skCap.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧ LayoutOk skCap.toNat 1)
      (by simp_all [rustDeallocExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, layoutOk_align1 hpos hlt⟩
      (by rw [hstack]; sep_focus)
      ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
    dsimp only [rustDeallocExternSpecWithStack]
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    have hst1 := hst.of_steps hF1 hsym1 rfl
      (by simp_all [hst.trace, arm64_norm])
      (by simp_all [hst.x26, arm64_norm])
      (by simp_all [hst.x27, arm64_norm])
      (by simp_all [hst.x28, arm64_norm])
    have hst2 := hst1.of_calleeSaved hsp2 hsp2_align hF2 hsym2 (htr2.trans hst1.trace) hcs2
    refine Wire.SepWPp.mono_pre
      (P' := memRegion x.ret 72 ∗ decodeErrorAt A errPtr ∗ A.pool ∗ stackAt s.sp (skipFieldStackX 100))
      (by apply entails_of_eq; rw [hstack]; ac_rfl) ?_
    exact hnext htry_err hst2 hpc2 hrun2
      (hcs2.1.trans (by simp_all [arm64_norm]))
      (hcs2.2.2.2.2.2.1.trans (by simp_all [arm64_norm]))
      (hcs2.2.1.trans (by simp_all [arm64_norm]))

theorem decodeErr_616_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsX img C A encFn decFn ext)
    (d : DecodeDeps img A ext)
    {x : DecodeGhost} {s0 s : State} {sp' ptr errPtr : BitVec 64}
    {bs : List (BitVec 8)} {mErr : IdentityKeyPairStructure}
    (htry_err : IdentityKeyPair.tryFrom x.bytes = .error .invalidProtobufEncoding)
    (hst : IkpBaseState img s0 sp' s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 616#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx24 : s.readReg64 .x24 = speWord 9)
    (hx20 : s.readReg64 .x20 = errPtr) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s
      (memRegion sp' 32 ∗
        memRegion (sp' + 32#64) 16 ∗
        ikpStructOf A (sp' + 48#64) mErr ∗
        memRegion (sp' + 96#64) 48 ∗
        ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗
        memRegion x.ret 72 ∗
        (ptr ↦ₛ bs) ∗
        logOff img ∗
        A.pool ∗
        stackAt sp' (skipFieldStackX 100) ∗
        decodeErrorAt A errPtr)
      (ikpExitPost img A s0 sp' x.ret ptr bs (IdentityKeyPair.tryFrom x.bytes))
      (tryFromQp s0) := by
  let H := Rust.withPanics ext
  have hnext := @decodeErr_640_wp img C A encFn decFn ext hC d x s0
  unfold ikpStructOf ikpStructAt
  simp only [vecU8At_eq_header_buf, vecHeader, BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun pk => Wire.SepWPp.exists_pre fun sk => ?_
  by_cases hcap : pk.cap = 0#64
  · rw [hcap, vecU8Buf_zero]
    simp only [sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun _ => ?_
    code_fetches_from CryptoVerification.libsignalSessionCode
      ikpTryFromBin img.base H
      (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
      (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))
      616 12
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr identityKeyPairTryFromName = entry
    examples_hide_fetches
    have hsp_subst := hst.sp
    subst hsp_subst
    have _hsp_align := hst.spAligned
    refine Wire.SepWPp.of_sepWP_frozen hst.frozen hst.symtab (mid := entry + bv% (640)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    intro hF1 hsym1
    have h144 := ikpFold144 s.sp 0#64 pk.ptr (BitVec.ofNat 64 mErr.publicKey.length)
      sk.cap sk.ptr (BitVec.ofNat 64 mErr.privateKey.length)
    dsimp only [vecHeader] at h144
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h144
    refine Wire.SepWPp.mono_pre
      (P' := (vecU8Buf A sk.cap sk.ptr mErr.privateKey ∗ memRegion x.ret 72 ∗
        decodeErrorAt A errPtr ∗ A.pool ∗ stackAt s.sp (skipFieldStackX 100)) ∗
        (memRegion s.sp 144 ∗ ((s.sp + 168#64) ↦₆₄ (s.sp + 32#64)) ∗
          (ptr ↦ₛ bs) ∗ logOff img))
      (by
        refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_left h144))
        apply entails_of_eq
        simp only [arm64_norm]
        ac_rfl) ?_
    refine Wire.SepWPp.frame_tryFrom
      (Q' := fun sf Pf => IkpBaseState img s0 s.sp sf ∧
        (Pf ⊢ identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
          A.pool ∗ stackAt s.sp (skipFieldStackX 100)))
      (hnext htry_err
        (hst.of_steps hF1 hsym1 rfl
          (by simp_all [hst.trace, arm64_norm])
          (by simp_all [hst.x26, arm64_norm])
          (by simp_all [hst.x27, arm64_norm])
          (by simp_all [hst.x28, arm64_norm]))
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]))
      fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
    unfold ikpExitMem
    refine Entails.trans (sepConj_mono_left hentf) ?_
    apply entails_of_eq; ac_rfl
  · have hd := vecU8Buf_dealloc A pk.cap pk.ptr mErr.publicKey hcap
    refine Wire.SepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hd)))))) ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hcall := ikp_dealloc_ok hC
    code_fetches_from CryptoVerification.libsignalSessionCode
      ikpTryFromBin img.base H
      (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
      (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))
      616 24
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr identityKeyPairTryFromName = entry
    examples_hide_fetches
    have hsp_subst := hst.sp
    subst hsp_subst
    have _hsp_align := hst.spAligned
    have hstack := stackAt_sub_split s.sp extHookStack (skipFieldStackX 100)
    have _hne : (pk.cap == 0#64) = false := beq_false_of_ne hcap
    refine Wire.SepWPp.of_sepWP_frozen hst.frozen hst.symtab
      (mid := entry + bv% ((ls_off% "__rustc::__rust_dealloc") -
        (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))) ?_
    wp_steps
    refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    intro hF1 hsym1
    refine Wire.SepWPp.call_noPanic_tryFrom (pk.ptr, pk.cap.toNat, 1) hcall
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by tryFromPost_sp_align hst.spAligned) hF1 hsym1
      (ret_pc := entry + bv% (640)) (by simp_all [arm64_norm])
      (T := A.pool ∗ A.live pk.ptr pk.cap.toNat 1 ∗ memRegion pk.ptr pk.cap.toNat ∗ stackAt s.sp extHookStack)
      (φ := pk.ptr = pk.ptr ∧ pk.cap.toNat = pk.cap.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧ LayoutOk pk.cap.toNat 1)
      (by simp_all [rustDeallocExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, layoutOk_align1 hpos hlt⟩
      (by rw [hstack]; sep_focus)
      ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
    dsimp only [rustDeallocExternSpecWithStack]
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    have hst1 := hst.of_steps hF1 hsym1 rfl
      (by simp_all [hst.trace, arm64_norm])
      (by simp_all [hst.x26, arm64_norm])
      (by simp_all [hst.x27, arm64_norm])
      (by simp_all [hst.x28, arm64_norm])
    have hst2 := hst1.of_calleeSaved hsp2 hsp2_align hF2 hsym2 (htr2.trans hst1.trace) hcs2
    have h144 := ikpFold144 s.sp pk.cap pk.ptr (BitVec.ofNat 64 mErr.publicKey.length)
      sk.cap sk.ptr (BitVec.ofNat 64 mErr.privateKey.length)
    dsimp only [vecHeader] at h144
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h144
    refine Wire.SepWPp.mono_pre
      (P' := (vecU8Buf A sk.cap sk.ptr mErr.privateKey ∗ memRegion x.ret 72 ∗
        decodeErrorAt A errPtr ∗ A.pool ∗ stackAt s.sp (skipFieldStackX 100)) ∗
        (memRegion s.sp 144 ∗ ((s.sp + 168#64) ↦₆₄ (s.sp + 32#64)) ∗
          (ptr ↦ₛ bs) ∗ logOff img))
      (by
        refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_left h144))
        apply entails_of_eq
        simp only [arm64_norm]
        rw [hstack]
        ac_rfl) ?_
    refine Wire.SepWPp.frame_tryFrom
      (Q' := fun sf Pf => IkpBaseState img s0 s.sp sf ∧
        (Pf ⊢ identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
          A.pool ∗ stackAt s.sp (skipFieldStackX 100)))
      (hnext htry_err hst2 hpc2 hrun2
        (hcs2.1.trans (by simp_all [arm64_norm]))
        (hcs2.2.2.2.2.2.1.trans (by simp_all [arm64_norm]))
        (hcs2.2.1.trans (by simp_all [arm64_norm]))
        (hcs2.2.2.1.trans (by simp_all [arm64_norm]))
        (hcs2.2.2.2.1.trans (by simp_all [arm64_norm])))
      fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
    unfold ikpExitMem
    refine Entails.trans (sepConj_mono_left hentf) ?_
    apply entails_of_eq; ac_rfl

theorem decodeErrorFrom_600_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsX img C A encFn decFn ext)
    (d : DecodeDeps img A ext)
    {x : DecodeGhost} {s0 s : State} {sp' ptr w0 : BitVec 64}
    {bs : List (BitVec 8)} {mErr : IdentityKeyPairStructure}
    (htry_err : IdentityKeyPair.tryFrom x.bytes = .error .invalidProtobufEncoding)
    (hregs : IkpLoopRegs img s0 sp' x.ret s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 600#64)
    (hrun : s.status = .Running)
    (hkind : KindNoHeap (s.readReg64 .x8)) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s
      (memRegion sp' 32 ∗
        memRegion (sp' + 32#64) 16 ∗
        ikpStructOf A (sp' + 48#64) mErr ∗
        ((sp' + 96#64) ↦₆₄ w0) ∗ memRegion (sp' + 104#64) 40 ∗
        ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗
        memRegion x.ret 72 ∗
        (ptr ↦ₛ bs) ∗
        logOff img ∗
        A.pool ∗
        stackAt sp' (skipFieldStackX 100))
      (ikpExitPost img A s0 sp' x.ret ptr bs (IdentityKeyPair.tryFrom x.bytes))
      (tryFromQp s0) := by
  let H := Rust.withPanics ext
  have hcall := ikp_decodeErrorFrom_ok hC
  have herr := @decodeErr_616_wp img C A encFn decFn ext hC d x s0
  code_fetches_from CryptoVerification.libsignalSessionCode
    ikpTryFromBin img.base H
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
    (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))
    600 16
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr identityKeyPairTryFromName = entry
  examples_hide_fetches
  have hsp_subst := hregs.base.sp
  subst hsp_subst
  have _hx29 := hregs.x29
  have hstack := stackAt_sub_split s.sp (2 * extHookStack) (skipFieldStackX 100)
  refine Wire.SepWPp.of_sepWP_frozen hregs.base.frozen hregs.base.symtab
    (mid := entry + bv% (
      (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from") -
      (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))) ?_
  wp_steps
  refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hF1 hsym1
  refine Wire.SepWPp.call_tryFrom (s.sp + 96#64, s.readReg64 (Reg.gpr 8#5)) hcall
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by tryFromPost_sp_align hregs.base.spAligned) hF1 hsym1
    (ret_pc := entry + bv% (612)) (by simp_all [arm64_norm])
    (by simp_all [hregs.base.trace, arm64_norm])
    (T := ((s.sp + 96#64) ↦₆₄ s.readReg64 (Reg.gpr 8#5)) ∗ memRegion (s.sp + 104#64) 40 ∗
      A.pool ∗ stackAt s.sp (2 * extHookStack))
    (φ := KindNoHeap (s.readReg64 (Reg.gpr 8#5)))
    (by simp_all [decodeErrorFromSpecWithStack, arm64_norm])
    hkind
    (by rw [hstack]; sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  have hregs1 := hregs.of_steps hF1 hsym1 rfl
    (by simp_all [hregs.base.trace, arm64_norm])
    (by simp_all [hregs.base.x26, arm64_norm])
    (by simp_all [hregs.base.x27, arm64_norm])
    (by simp_all [hregs.base.x28, arm64_norm])
    (by simp_all [arm64_norm]) (by simp_all [hregs.x19, arm64_norm])
    (by simp_all [hregs.x21, arm64_norm]) (by simp_all [hregs.x24, arm64_norm])
  dsimp only [decodeErrorFromSpecWithStack]
  rw [sepConj_assoc]
  refine Wire.SepWPp.pure_pre fun ⟨_hx0_ne, htr2⟩ => ?_
  have hregs2' := hregs1.of_calleeSaved hsp2 hsp2_align hF2 hsym2
    (htr2.trans hregs1.base.trace) hcs2
  refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + bv% (616)) ?_
  wp_steps
  refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hF3 hsym3
  refine Wire.SepWPp.mono_pre
    (P' := memRegion s.sp 32 ∗
      memRegion (s.sp + 32#64) 16 ∗
      ikpStructOf A (s.sp + 48#64) mErr ∗
      memRegion (s.sp + 96#64) 48 ∗
      ((s.sp + 168#64) ↦₆₄ (s.sp + 32#64)) ∗
      memRegion x.ret 72 ∗
      (ptr ↦ₛ bs) ∗
      logOff img ∗
      A.pool ∗
      stackAt s.sp (skipFieldStackX 100) ∗
      decodeErrorAt A (s2.readReg64 (Reg.gpr 0#5)))
    (by
      simp only [arm64_norm]
      rw [hstack]
      refine Entails.trans
        (sepConj_mono (decodeErrorWith_entails_at A (s2.readReg64 (Reg.gpr 0#5)) 0)
          (Entails.refl _)) ?_
      apply entails_of_eq; ac_rfl) ?_
  exact herr htry_err
    (hregs2'.base.of_steps hF3 hsym3
      (by simp_all [hregs2'.base.sp, arm64_norm])
      (by simp_all [hregs2'.base.trace, arm64_norm])
      (by simp_all [hregs2'.base.x26, arm64_norm])
      (by simp_all [hregs2'.base.x27, arm64_norm])
      (by simp_all [hregs2'.base.x28, arm64_norm]))
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [hregs2'.x19, arm64_norm])
    (by simp_all [hregs2'.x24, arm64_norm])
    (by simp_all [arm64_norm])

theorem decodeErrorPush_916_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsX img C A encFn decFn ext)
    (d : DecodeDeps img A ext)
    {x : DecodeGhost} {s0 s : State} {sp' ptr err : BitVec 64}
    {n : Nat} {bs : List (BitVec 8)} {mErr : IdentityKeyPairStructure}
    (htry_err : IdentityKeyPair.tryFrom x.bytes = .error .invalidProtobufEncoding)
    (hregs : IkpLoopRegs img s0 sp' x.ret s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 916#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = sp' + 96#64)
    (herr_ne : err ≠ 0#64) (hn : n < 2 ^ 32) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s
      (memRegion sp' 32 ∗
        memRegion (sp' + 32#64) 16 ∗
        ikpStructOf A (sp' + 48#64) mErr ∗
        ((sp' + 96#64) ↦₆₄ err) ∗ memRegion (sp' + 104#64) 40 ∗
        ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗
        memRegion x.ret 72 ∗
        (ptr ↦ₛ bs) ∗
        logOff img ∗
        A.pool ∗
        stackAt sp' (skipFieldStackX 100) ∗
        decodeErrorAtStackLen A err n)
      (ikpExitPost img A s0 sp' x.ret ptr bs (IdentityKeyPair.tryFrom x.bytes))
      (tryFromQp s0) := by
  let H := Rust.withPanics ext
  have hcall := ikp_decodeErrorPush_ok hC
  have herr := @decodeErr_616_wp img C A encFn decFn ext hC d x s0
  code_fetches_from CryptoVerification.libsignalSessionCode
    ikpTryFromBin img.base H
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
    (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))
    916 12
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr identityKeyPairTryFromName = entry
  examples_hide_fetches
  have hsp_subst := hregs.base.sp
  subst hsp_subst
  have hstack := stackAt_sub_split s.sp (2 * extHookStack) (skipFieldStackX 100)
  refine Wire.SepWPp.of_sepWP_frozen hregs.base.frozen hregs.base.symtab
    (mid := entry + bv% (
      (ls_off% "<prost::error::DecodeError>::push") -
      (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))) ?_
  wp_steps
  refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hF1 hsym1
  refine Wire.SepWPp.call_tryFrom (s.sp + 96#64, err, n) hcall
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by tryFromPost_sp_align hregs.base.spAligned) hF1 hsym1
    (ret_pc := entry + bv% (920)) (by simp_all [arm64_norm])
    (by simp_all [hregs.base.trace, arm64_norm])
    (T := ((s.sp + 96#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A err n ∗
      A.pool ∗ stackAt s.sp (2 * extHookStack))
    (φ := err ≠ 0#64 ∧ n < 4294967296)
    (by simp_all [decodeErrorPushExternSpecWithStack, arm64_norm])
    ⟨herr_ne, hn⟩
    (by rw [hstack]; sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  dsimp only [decodeErrorPushExternSpecWithStack]
  rw [sepConj_assoc]
  refine Wire.SepWPp.pure_pre fun htr2 => ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun err' => ?_
  refine Wire.SepWPp.pure_pre fun _herr' => ?_
  have hregs1 := hregs.of_steps hF1 hsym1 rfl
    (by simp_all [hregs.base.trace, arm64_norm])
    (by simp_all [hregs.base.x26, arm64_norm])
    (by simp_all [hregs.base.x27, arm64_norm])
    (by simp_all [hregs.base.x28, arm64_norm])
    (by simp_all [hregs.x29, arm64_norm]) (by simp_all [hregs.x19, arm64_norm])
    (by simp_all [hregs.x21, arm64_norm]) (by simp_all [hregs.x24, arm64_norm])
  have hregs2 := hregs1.of_calleeSaved hsp2 hsp2_align hF2 hsym2
    (htr2.trans hregs1.base.trace) hcs2
  have _hx29_2 := hregs2.x29
  refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + bv% (616)) ?_
  wp_steps
  refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hF3 hsym3
  have hm48 := ikpPointsTo64_96_mem40_entails_mem48 s.sp err'
  refine Wire.SepWPp.mono_pre
    (P' := memRegion s.sp 32 ∗
      memRegion (s.sp + 32#64) 16 ∗
      ikpStructOf A (s.sp + 48#64) mErr ∗
      memRegion (s.sp + 96#64) 48 ∗
      ((s.sp + 168#64) ↦₆₄ (s.sp + 32#64)) ∗
      memRegion x.ret 72 ∗
      (ptr ↦ₛ bs) ∗
      logOff img ∗
      A.pool ∗
      stackAt s.sp (skipFieldStackX 100) ∗
      decodeErrorAt A err')
    (by
      simp only [arm64_norm]
      rw [hstack]
      refine Entails.trans
        (sepConj_mono_right (sepConj_mono
          (decodeErrorWith_entails_at A err' (n + 1)) (Entails.refl _))) ?_
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hm48))))
      apply entails_of_eq; ac_rfl) ?_
  exact herr htry_err
    (hregs2.base.of_steps hF3 hsym3
      (by simp_all [hregs2.base.sp, arm64_norm])
      (by simp_all [hregs2.base.trace, arm64_norm])
      (by simp_all [hregs2.base.x26, arm64_norm])
      (by simp_all [hregs2.base.x27, arm64_norm])
      (by simp_all [hregs2.base.x28, arm64_norm]))
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [hregs2.x19, arm64_norm])
    (by simp_all [hregs2.x24, arm64_norm])
    (by simp_all [arm64_norm])


def ikpLoopCommon (img : Obj.Image) (A : RustAlloc) (sp' ret : BitVec 64)
    (len : Nat) (m : IdentityKeyPairStructure) : SepProp :=
  memRegion sp' 32 ∗
    ikpStructLoopOf A (sp' + 48#64) len m ∗
    memRegion (sp' + 96#64) 48 ∗
    ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗
    memRegion ret 72 ∗
    logOff img ∗
    A.pool ∗
    stackAt sp' (skipFieldStackX 100)

section Placed

open CryptoVerification.RecordCodecs.Placed

def ikpExitMemPlaced [LibsignalPlacement] (A : RustAlloc) (sp' ret ptr : BitVec 64)
    (bs : List (BitVec 8)) (out : Except SignalProtocolError IdentityKeyPair) : SepProp :=
  memRegion sp' 144 ∗ ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗
    identityKeyPairResultAt A ret out ∗ (ptr ↦ₛ bs) ∗
    lsLogOff ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100)

def ikpExitPostPlaced [LibsignalPlacement] (A : RustAlloc) (s0 : State)
    (sp' ret ptr : BitVec 64) (bs : List (BitVec 8))
    (out : Except SignalProtocolError IdentityKeyPair) (sf : State) (Pf : SepProp) : Prop :=
  IkpBaseStatePlaced s0 sp' sf ∧ (Pf ⊢ ikpExitMemPlaced A sp' ret ptr bs out)

theorem IkpLoopRegsPlaced.of_steps [LibsignalPlacement] {s0 s1 s2 : State} {sp' ret : BitVec 64}
    (hr : IkpLoopRegsPlaced s0 sp' ret s1) (hcrl : LibsignalCodeRoLoaded lsmpl s2.mem)
    (hsp : s2.sp = sp') (htr : s2.trace = s0.trace)
    (h26 : s2.readReg64 .x26 = s0.readReg64 .x26)
    (h27 : s2.readReg64 .x27 = s0.readReg64 .x27)
    (h28 : s2.readReg64 .x28 = s0.readReg64 .x28)
    (h29 : s2.readReg64 .x29 = sp' + 144#64) (h19 : s2.readReg64 .x19 = ret)
    (h21 : s2.readReg64 .x21 = sp' + 48#64) (h24 : s2.readReg64 .x24 = speWord 9) :
    IkpLoopRegsPlaced s0 sp' ret s2 where
  base := hr.base.of_steps hcrl hsp htr h26 h27 h28
  x29 := h29
  x19 := h19
  x21 := h21
  x24 := h24

theorem ikp_advance_cursor_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {s0 s : State} {sp' ret ptr : BitVec 64} {bs rest : List (BitVec 8)} {k : Nat}
    {R : SepProp} {out : Except SignalProtocolError IdentityKeyPair}
    (hkl : k ≤ bs.length) (hrest : rest = bs.drop k)
    (hsub : Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + bv% (812)) s
      (sliceCursorAt (sp' + 32#64) (ptr + BitVec.ofNat 64 k) rest ∗ R)
      (ikpExitPostPlaced A s0 sp' ret (ptr + BitVec.ofNat 64 k) rest out) (tryFromQp s0)) :
    Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + bv% (812)) s
      (sliceCursorAfter (sp' + 32#64) ptr bs rest ∗ R)
      (ikpExitPostPlaced A s0 sp' ret ptr bs out) (tryFromQp s0) := by
  have hk_eq : bs.length - rest.length = k := by rw [hrest, List.length_drop]; omega
  have hsplit := pointsToBytes_take_drop k bs ptr hkl
  rw [← hrest] at hsplit
  refine Wire.SepWPp.mono_pre
    (P' := (sliceCursorAt (sp' + 32#64) (ptr + BitVec.ofNat 64 k) rest ∗ R) ∗ (ptr ↦ₛ bs.take k))
    (by unfold sliceCursorAfter sliceCursorAt; rw [hk_eq, hsplit]; apply entails_of_eq; ac_rfl) ?_
  refine Wire.SepWPp.frame_tryFrom
    (Q' := ikpExitPostPlaced A s0 sp' ret (ptr + BitVec.ofNat 64 k) rest out)
    hsub fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
  refine Entails.trans (sepConj_mono_left hentf) ?_
  unfold ikpExitMemPlaced; rw [hsplit]; apply entails_of_eq; ac_rfl

theorem decodeErr_660_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) {x : DecodeGhost} {s0 s : State} {sp' errPtr : BitVec 64}
    (htry_err : IdentityKeyPair.tryFrom x.bytes = .error .invalidProtobufEncoding)
    (hst : IkpBaseStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_84).base + bv% (660)) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x.ret) (hx24 : s.readReg64 .x24 = speWord 9)
    (hx20 : s.readReg64 .x20 = errPtr) :
    Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + bv% (812)) s
      (memRegion x.ret 72 ∗ decodeErrorAt A errPtr ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => IkpBaseStatePlaced s0 sp' sf ∧
        (Pf ⊢ identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  have hcall := ikp_dropDecodeError_placed_ok d
  refine Wire.SepWPp.mono_pre (sepConj_mono_left (memRegion72_split_err x.ret)) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun w2 => Wire.SepWPp.exists_pre fun w1 =>
    Wire.SepWPp.exists_pre fun b0 => ?_
  have hsp_subst := hst.sp; subst hsp_subst
  have hstack := stackAt_sub_split s.sp dropDecodeErrorStackX (skipFieldStackX 100)
  refine sepWPp_of_sepWP_lscro hst.crl (mid := lsmpl.base 4) ?_; wp_steps
  refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_; intro hcrl1
  refine sepWPp_call_noPanic_lscro errPtr hcall
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by tryFromPost_sp_align hst.spAligned) hcrl1
    (by simp_all [arm64_norm] : _ = (blkPl_84).base + bv% (668))
    (by simp_all [hst.trace, arm64_norm])
    (T := decodeErrorAt A errPtr ∗ A.pool ∗ stackAt s.sp dropDecodeErrorStackX)
    (φ := errPtr = errPtr) (by simp_all [dropDecodeErrorSpecX, arm64_norm])
    rfl (by rw [hstack]; sep_focus) ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  dsimp only [dropDecodeErrorSpecX]; rw [sepConj_assoc]
  refine Wire.SepWPp.pure_pre fun htr2 => ?_
  have hx19_2 : s2.readReg64 .x19 = x.ret := hcs2.1.trans (by simp_all [arm64_norm])
  have hx24_2 : s2.readReg64 .x24 = speWord 9 := hcs2.2.2.2.2.2.1.trans (by simp_all [arm64_norm])
  refine sepWPp_of_sepWP_end_lscro hcrl2 ?_; wp_steps
  refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_; intro hcrl3
  have hst1 := hst.of_steps hcrl1 rfl
    (by simp_all [hst.trace, arm64_norm]) (by simp_all [hst.x26, arm64_norm])
    (by simp_all [hst.x27, arm64_norm]) (by simp_all [hst.x28, arm64_norm])
  have hst2 := hst1.of_calleeSaved hsp2 hsp2_align hcrl2 (htr2.trans hst1.trace) hcs2
  refine ⟨hst2.of_steps hcrl3 (by simp_all [hst2.sp, arm64_norm])
    (by simp_all [hst2.trace, arm64_norm]) (by simp_all [hst2.x26, arm64_norm])
    (by simp_all [hst2.x27, arm64_norm]) (by simp_all [hst2.x28, arm64_norm]), ?_⟩
  have hspe : speWord 9 - 7#64 = speWord 2 := rfl
  have hres := ikpResult_err_spe2 A x.ret w2 htry_err
  simp only [arm64_norm, hspe]
  refine Entails.trans ?_ (sepConj_mono hres (Entails.refl _))
  apply entails_of_eq; rw [hstack]; ac_rfl

theorem decodeErr_640_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) {x : DecodeGhost} {s0 s : State}
    {sp' skCap skPtr errPtr : BitVec 64} {skBs : List (BitVec 8)}
    (htry_err : IdentityKeyPair.tryFrom x.bytes = .error .invalidProtobufEncoding)
    (hst : IkpBaseStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_84).base + bv% (640)) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x.ret) (hx24 : s.readReg64 .x24 = speWord 9)
    (hx20 : s.readReg64 .x20 = errPtr) (hx21 : s.readReg64 .x21 = skCap)
    (hx22 : s.readReg64 .x22 = skPtr) :
    Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + bv% (812)) s
      (vecU8Buf A skCap skPtr skBs ∗ memRegion x.ret 72 ∗
        decodeErrorAt A errPtr ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => IkpBaseStatePlaced s0 sp' sf ∧
        (Pf ⊢ identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  have hnext := @decodeErr_660_placed_wp _ A H d x s0
  by_cases hcap : skCap = 0#64
  · subst hcap; rw [vecU8Buf_zero]; refine Wire.SepWPp.pure_pre fun _ => ?_
    have _hsp_eq := hst.sp
    refine sepWPp_of_sepWP_lscro hst.crl (mid := (blkPl_84).base + bv% (660)) ?_; wp_steps
    refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_; intro hcrl1
    exact hnext htry_err
      (hst.of_steps hcrl1 (by simp_all [arm64_norm]) (by simp_all [hst.trace, arm64_norm])
        (by simp_all [hst.x26, arm64_norm]) (by simp_all [hst.x27, arm64_norm])
        (by simp_all [hst.x28, arm64_norm]))
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  · refine Wire.SepWPp.mono_pre (sepConj_mono_left (vecU8Buf_dealloc A skCap skPtr skBs hcap)) ?_
    simp only [sepConj_assoc]; refine Wire.SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hcall := ikp_dealloc_placed_ok d
    have hsp_subst := hst.sp; subst hsp_subst
    have hstack := stackAt_sub_split s.sp extHookStack (skipFieldStackX 100)
    have _hne : (skCap == 0#64) = false := beq_false_of_ne hcap
    refine sepWPp_of_sepWP_lscro hst.crl (mid := lsρ lsRustDeallocSym) ?_; wp_steps
    refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_; intro hcrl1
    refine sepWPp_call_noPanic_lscro (skPtr, skCap.toNat, 1) hcall
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by tryFromPost_sp_align hst.spAligned) hcrl1
      (by simp_all [arm64_norm] : _ = (blkPl_84).base + bv% (660))
      (by simp_all [hst.trace, arm64_norm])
      (T := A.pool ∗ A.live skPtr skCap.toNat 1 ∗ memRegion skPtr skCap.toNat ∗ stackAt s.sp extHookStack)
      (φ := skPtr = skPtr ∧ skCap.toNat = skCap.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧ LayoutOk skCap.toNat 1)
      (by simp_all [rustDeallocExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, layoutOk_align1 hpos hlt⟩ (by rw [hstack]; sep_focus) ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack]; rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    have hst1 := hst.of_steps hcrl1 rfl
      (by simp_all [hst.trace, arm64_norm]) (by simp_all [hst.x26, arm64_norm])
      (by simp_all [hst.x27, arm64_norm]) (by simp_all [hst.x28, arm64_norm])
    have hst2 := hst1.of_calleeSaved hsp2 hsp2_align hcrl2 (htr2.trans hst1.trace) hcs2
    refine Wire.SepWPp.mono_pre
      (P' := memRegion x.ret 72 ∗ decodeErrorAt A errPtr ∗ A.pool ∗ stackAt s.sp (skipFieldStackX 100))
      (by apply entails_of_eq; rw [hstack]; ac_rfl) ?_
    exact hnext htry_err hst2 hpc2 hrun2
      (hcs2.1.trans (by simp_all [arm64_norm]))
      (hcs2.2.2.2.2.2.1.trans (by simp_all [arm64_norm]))
      (hcs2.2.1.trans (by simp_all [arm64_norm]))

theorem decodeErr_616_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) {x : DecodeGhost} {s0 s : State} {sp' ptr errPtr : BitVec 64}
    {bs : List (BitVec 8)} {mErr : IdentityKeyPairStructure}
    (htry_err : IdentityKeyPair.tryFrom x.bytes = .error .invalidProtobufEncoding)
    (hst : IkpBaseStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_84).base + bv% (616)) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x.ret) (hx24 : s.readReg64 .x24 = speWord 9)
    (hx20 : s.readReg64 .x20 = errPtr) :
    Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + bv% (812)) s
      (memRegion sp' 32 ∗ memRegion (sp' + 32#64) 16 ∗ ikpStructOf A (sp' + 48#64) mErr ∗
        memRegion (sp' + 96#64) 48 ∗ ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗
        memRegion x.ret 72 ∗ (ptr ↦ₛ bs) ∗ lsLogOff ∗ A.pool ∗
        stackAt sp' (skipFieldStackX 100) ∗ decodeErrorAt A errPtr)
      (ikpExitPostPlaced A s0 sp' x.ret ptr bs (IdentityKeyPair.tryFrom x.bytes))
      (tryFromQp s0) := by
  have hnext := @decodeErr_640_placed_wp _ A H d x s0
  unfold ikpStructOf ikpStructAt
  simp only [vecU8At_eq_header_buf, vecHeader, BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun pk => Wire.SepWPp.exists_pre fun sk => ?_
  by_cases hcap : pk.cap = 0#64
  · rw [hcap, vecU8Buf_zero]; simp only [sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun _ => ?_
    have hsp_subst := hst.sp; subst hsp_subst
    have _hsp_align := hst.spAligned
    refine sepWPp_of_sepWP_lscro hst.crl (mid := (blkPl_84).base + bv% (640)) ?_; wp_steps
    refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_; intro hcrl1
    have h144 := ikpFold144 s.sp 0#64 pk.ptr (BitVec.ofNat 64 mErr.publicKey.length)
      sk.cap sk.ptr (BitVec.ofNat 64 mErr.privateKey.length)
    dsimp only [vecHeader] at h144; simp only [BitVec.add_assoc, BitVec.reduceAdd] at h144
    refine Wire.SepWPp.mono_pre
      (P' := (vecU8Buf A sk.cap sk.ptr mErr.privateKey ∗ memRegion x.ret 72 ∗
        decodeErrorAt A errPtr ∗ A.pool ∗ stackAt s.sp (skipFieldStackX 100)) ∗
        (memRegion s.sp 144 ∗ ((s.sp + 168#64) ↦₆₄ (s.sp + 32#64)) ∗ (ptr ↦ₛ bs) ∗ lsLogOff))
      (by refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_left h144))
          apply entails_of_eq; simp only [arm64_norm]; ac_rfl) ?_
    refine Wire.SepWPp.frame_tryFrom
      (Q' := fun sf Pf => IkpBaseStatePlaced s0 s.sp sf ∧
        (Pf ⊢ identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
          A.pool ∗ stackAt s.sp (skipFieldStackX 100)))
      (hnext htry_err
        (hst.of_steps hcrl1 rfl (by simp_all [hst.trace, arm64_norm])
          (by simp_all [hst.x26, arm64_norm]) (by simp_all [hst.x27, arm64_norm])
          (by simp_all [hst.x28, arm64_norm]))
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm]))
      fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
    unfold ikpExitMemPlaced; refine Entails.trans (sepConj_mono_left hentf) ?_
    apply entails_of_eq; ac_rfl
  · have hd := vecU8Buf_dealloc A pk.cap pk.ptr mErr.publicKey hcap
    refine Wire.SepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hd)))))) ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hcall := ikp_dealloc_placed_ok d
    have hsp_subst := hst.sp; subst hsp_subst
    have _hsp_align := hst.spAligned
    have hstack := stackAt_sub_split s.sp extHookStack (skipFieldStackX 100)
    have _hne : (pk.cap == 0#64) = false := beq_false_of_ne hcap
    refine sepWPp_of_sepWP_lscro hst.crl (mid := lsρ lsRustDeallocSym) ?_; wp_steps
    refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_; intro hcrl1
    refine sepWPp_call_noPanic_lscro (pk.ptr, pk.cap.toNat, 1) hcall
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by tryFromPost_sp_align hst.spAligned) hcrl1
      (by simp_all [arm64_norm] : _ = (blkPl_84).base + bv% (640))
      (by simp_all [hst.trace, arm64_norm])
      (T := A.pool ∗ A.live pk.ptr pk.cap.toNat 1 ∗ memRegion pk.ptr pk.cap.toNat ∗ stackAt s.sp extHookStack)
      (φ := pk.ptr = pk.ptr ∧ pk.cap.toNat = pk.cap.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧ LayoutOk pk.cap.toNat 1)
      (by simp_all [rustDeallocExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, layoutOk_align1 hpos hlt⟩ (by rw [hstack]; sep_focus) ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack]; rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    have hst1 := hst.of_steps hcrl1 rfl
      (by simp_all [hst.trace, arm64_norm]) (by simp_all [hst.x26, arm64_norm])
      (by simp_all [hst.x27, arm64_norm]) (by simp_all [hst.x28, arm64_norm])
    have hst2 := hst1.of_calleeSaved hsp2 hsp2_align hcrl2 (htr2.trans hst1.trace) hcs2
    have h144 := ikpFold144 s.sp pk.cap pk.ptr (BitVec.ofNat 64 mErr.publicKey.length)
      sk.cap sk.ptr (BitVec.ofNat 64 mErr.privateKey.length)
    dsimp only [vecHeader] at h144; simp only [BitVec.add_assoc, BitVec.reduceAdd] at h144
    refine Wire.SepWPp.mono_pre
      (P' := (vecU8Buf A sk.cap sk.ptr mErr.privateKey ∗ memRegion x.ret 72 ∗
        decodeErrorAt A errPtr ∗ A.pool ∗ stackAt s.sp (skipFieldStackX 100)) ∗
        (memRegion s.sp 144 ∗ ((s.sp + 168#64) ↦₆₄ (s.sp + 32#64)) ∗ (ptr ↦ₛ bs) ∗ lsLogOff))
      (by refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_left h144))
          apply entails_of_eq; simp only [arm64_norm]; rw [hstack]; ac_rfl) ?_
    refine Wire.SepWPp.frame_tryFrom
      (Q' := fun sf Pf => IkpBaseStatePlaced s0 s.sp sf ∧
        (Pf ⊢ identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
          A.pool ∗ stackAt s.sp (skipFieldStackX 100)))
      (hnext htry_err hst2 hpc2 hrun2
        (hcs2.1.trans (by simp_all [arm64_norm]))
        (hcs2.2.2.2.2.2.1.trans (by simp_all [arm64_norm]))
        (hcs2.2.1.trans (by simp_all [arm64_norm]))
        (hcs2.2.2.1.trans (by simp_all [arm64_norm]))
        (hcs2.2.2.2.1.trans (by simp_all [arm64_norm])))
      fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
    unfold ikpExitMemPlaced; refine Entails.trans (sepConj_mono_left hentf) ?_
    apply entails_of_eq; ac_rfl

def ikpLoopCommonPlaced [LibsignalPlacement] (A : RustAlloc) (sp' ret : BitVec 64)
    (len : Nat) (m : IdentityKeyPairStructure) : SepProp :=
  memRegion sp' 32 ∗ ikpStructLoopOf A (sp' + 48#64) len m ∗
    memRegion (sp' + 96#64) 48 ∗ ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗
    memRegion ret 72 ∗ lsLogOff ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100)

end Placed

end CryptoVerification.RecordCodecsBinary.IdentityKeyPairTryFrom.Helpers
