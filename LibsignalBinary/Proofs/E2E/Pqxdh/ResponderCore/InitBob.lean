/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.Accept
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCallees
import GeneratedLean.LibsignalSessionCode -- shake: keep
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace CryptoVerification.E2E.Pqxdh.ResponderCore

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession
  CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

local macro "cells_unfold_fast" : tactic =>
  `(tactic| simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit',
    BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub])


theorem SepWPp.of_sepWP_frozen_inImage {prog : Program} {img : Obj.Image} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hwp : SepWP prog mid s P (fun sm Pm =>
      img.FrozenLoaded sm → sm.symtab = img.symtab → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨_, _, Pm, hmm, hnext⟩ | ⟨_, hoom⟩⟩ := hwp.elim hm hL
  · obtain ⟨sf, hsteps', hout⟩ :=
      hnext (hF.of_keepsFrozen hsteps.keepsFrozen) (hsteps.symtab_eq.trans hsym)
        R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem SepWPp.call_inImage_frame {α : Type} {prog : Program} {img : Obj.Image}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗
      R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro sf; first | rfl | simp only [Spec.inImage]) :
    SepWPp prog ret s P Q Qp := by
  refine ProofLib.SepWPp.call_inImage_frame (x := x) (T := T) (F := F)
    hcall hF hsym hpc hrun hsp hlr hspec hφ hP hexit hpanic
    (fun sf hpcm hrunm hspm hcsm hFm hsymm =>
      hnext sf hpcm hrunm hspm (by simpa [State.spAligned, hspm] using hsp) hcsm hFm hsymm)
    (fun sf R' _ hoom_post => by
      rw [hoom sf] at hoom_post
      exact (not_satisfies_false_sepConj hoom_post).elim)

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64

def bobHead144Bv8 (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr :
    BitVec 64) : List (BitVec 8) :=
  unpack64 33#64 ++ unpack64 localIkBoxPtr ++ unpack64 33#64 ++
  unpack64 33#64 ++ unpack64 remoteIkBoxPtr ++ unpack64 33#64 ++
  unpack64 32#64 ++ unpack64 rootKeyBoxPtr ++ unpack64 32#64 ++
  unpack64 0#64 ++ unpack64 8#64 ++ unpack64 0#64 ++
  unpack64 33#64 ++ unpack64 baseKeyBoxPtr ++ unpack64 33#64 ++
  unpack64 spqrCap ++ unpack64 spqrBufPtr ++ unpack64 0#64

@[simp]
theorem bobHead144Bv8_length (p1 p2 p3 p4 c5 p5 : BitVec 64) :
    (bobHead144Bv8 p1 p2 p3 p4 c5 p5).length = 144 := by
  simp [bobHead144Bv8]

theorem bobHead144_eq_pointsToBytes (ptr : BitVec 64)
    (p1 p2 p3 p4 c5 p5 : BitVec 64) :
    (ptr ↦₆₄ 33#64) ∗
    ((ptr + 0x08#64) ↦₆₄ p1) ∗
    ((ptr + 0x10#64) ↦₆₄ 33#64) ∗
    ((ptr + 0x18#64) ↦₆₄ 33#64) ∗
    ((ptr + 0x20#64) ↦₆₄ p2) ∗
    ((ptr + 0x28#64) ↦₆₄ 33#64) ∗
    ((ptr + 0x30#64) ↦₆₄ 32#64) ∗
    ((ptr + 0x38#64) ↦₆₄ p3) ∗
    ((ptr + 0x40#64) ↦₆₄ 32#64) ∗
    ((ptr + 0x48#64) ↦₆₄ 0#64) ∗
    ((ptr + 0x50#64) ↦₆₄ 8#64) ∗
    ((ptr + 0x58#64) ↦₆₄ 0#64) ∗
    ((ptr + 0x60#64) ↦₆₄ 33#64) ∗
    ((ptr + 0x68#64) ↦₆₄ p4) ∗
    ((ptr + 0x70#64) ↦₆₄ 33#64) ∗
    ((ptr + 0x78#64) ↦₆₄ c5) ∗
    ((ptr + 0x80#64) ↦₆₄ p5) ∗
    ((ptr + 0x88#64) ↦₆₄ 0#64) =
      (ptr ↦ₛ bobHead144Bv8 p1 p2 p3 p4 c5 p5) := by
  unfold bobHead144Bv8
  simp only [List.append_assoc, pointsToBytes_append, unpack64_length,
    BitVec.add_assoc, BitVec.reduceAdd, ← pointsTo64_eq_pointsToBytes]

def bobTail96Bv8 (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) : List (BitVec 8) :=
  unpack64 0xffffffffffffffff#64 ++
  unpack64 c0 ++ unpack64 c1 ++ unpack64 c2 ++ unpack64 c3 ++ unpack64 c4 ++
  unpack64 0xffffffffffffffff#64 ++
  unpack64 d0 ++ unpack64 d1 ++ unpack64 d2 ++
  unpack64 4#64 ++ unpack64 0#64

@[simp]
theorem bobTail96Bv8_length (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) :
    (bobTail96Bv8 c0 c1 c2 c3 c4 d0 d1 d2).length = 96 := by
  simp [bobTail96Bv8]

theorem bobTail96_eq_pointsToBytes (ptr : BitVec 64)
    (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) :
    ((ptr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗
    ((ptr + 0x100#64) ↦₆₄ c0) ∗
    ((ptr + 0x108#64) ↦₆₄ c1) ∗
    ((ptr + 0x110#64) ↦₆₄ c2) ∗
    ((ptr + 0x118#64) ↦₆₄ c3) ∗
    ((ptr + 0x120#64) ↦₆₄ c4) ∗
    ((ptr + 0x128#64) ↦₆₄ 0xffffffffffffffff#64) ∗
    ((ptr + 0x130#64) ↦₆₄ d0) ∗
    ((ptr + 0x138#64) ↦₆₄ d1) ∗
    ((ptr + 0x140#64) ↦₆₄ d2) ∗
    ((ptr + 0x148#64) ↦₆₄ 4#64) ∗
    ((ptr + 0x150#64) ↦₆₄ 0#64) =
      ((ptr + 0xf8#64) ↦ₛ bobTail96Bv8 c0 c1 c2 c3 c4 d0 d1 d2) := by
  unfold bobTail96Bv8
  simp only [List.append_assoc, pointsToBytes_append, unpack64_length,
    BitVec.add_assoc, BitVec.reduceAdd, ← pointsTo64_eq_pointsToBytes]

def bobSession344Bv8 (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
    ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) : List (BitVec 8) :=
  bobHead144Bv8 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr ++
  senderChainBytes100 ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr 0#32 ++ unpack32 pad_f4 ++
  bobTail96Bv8 c0 c1 c2 c3 c4 d0 d1 d2

@[simp]
theorem bobSession344Bv8_length (p1 p2 p3 p4 c5 p5 p6 p7 p8 : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) :
    (bobSession344Bv8 p1 p2 p3 p4 c5 p5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2).length = 344 := by
  simp [bobSession344Bv8]

theorem hkdfDerive96_lengths (P : Primitives) (hWF : StructuralPrims P) (secrets : Bytes) :
    (P.hkdfDerive96 secrets).rootKey.length = 32 ∧
    (P.hkdfDerive96 secrets).pqrKey.length = 32 ∧
    (P.hkdfDerive96 secrets).chainKey.length = 32 := by
  rw [hWF.hkdfDerive96_eq_ref secrets]
  unfold hkdfDerive96Ref hkdfExpand96Ref
  refine ⟨hmacSha256Ref_length P _ _, hmacSha256Ref_length P _ _, hmacSha256Ref_length P _ _⟩

theorem acceptKeys_some_lengths {P : Primitives} {inp : AcceptKeysInput} {drKey : DRKey}
    (hWF : StructuralPrims P) (h : Model.acceptKeys P inp = some drKey) :
    drKey.rootKey.length = 32 ∧ drKey.pqrKey.length = 32 ∧ drKey.chainKey.length = 32 := by
  unfold Model.acceptKeys at h
  simp only [bind, Option.bind_eq_some_iff] at h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h⟩
  split at h
  · simp only [Option.bind_some, Option.bind_eq_some_iff, Option.some.injEq] at h
    rcases h with ⟨_, _, ss, _, rfl⟩
    exact hkdfDerive96_lengths P hWF _
  · simp only [Option.bind_some, Option.bind_eq_some_iff, Option.some.injEq] at h
    rcases h with ⟨_, _, ss, _, rfl⟩
    exact hkdfDerive96_lengths P hWF _
  · simp only [Option.bind_none, reduceCtorEq] at h

theorem split_word_0x1000007d0 (p : BitVec 64) :
    (p ↦₆₄ 0x1000007d0#64) =
      (p ↦₃₂ 0x7d0#32) ∗
      ((p + 4#64) ↦ₛ bytesToBv8 [1]) ∗
      ((p + 5#64) ↦ₛ [0#8, 0#8, 0#8]) := by
  have h : unpack64 0x1000007d0#64 = unpack32 0x7d0#32 ++ (bytesToBv8 [1] ++ [0#8, 0#8, 0#8]) := by
    decide
  rw [pointsTo64_eq_pointsToBytes, h, pointsToBytes_append, unpack32_length,
    pointsToBytes_append, show (bytesToBv8 [1]).length = 1 from rfl,
    ← pointsTo32_eq_pointsToBytes]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem realign_4_8_8_to_8_8_4 (p : BitVec 64) (w0 : BitVec 32) (u0 u1 : BitVec 64) :
    (p ↦₃₂ w0) ∗ ((p + 4#64) ↦₆₄ u0) ∗ ((p + 12#64) ↦₆₄ u1) ⊢
      ∃∗ w1 : BitVec 32, ∃∗ v1 : BitVec 64, ∃∗ v0 : BitVec 64,
        (p ↦₆₄ v0) ∗ ((p + 8#64) ↦₆₄ v1) ∗ ((p + 16#64) ↦₃₂ w1) := by
  have hm1 : (p ↦₃₂ w0) ∗ ((p + 4#64) ↦₆₄ u0) ∗ ((p + 12#64) ↦₆₄ u1) ⊢ memRegion p 20 := by
    rw [memRegion_split p 4 16 (by decide),
      memRegion_split (p + 4#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono (pointsTo32_entails_memRegion p w0)
      (sepConj_mono (pointsTo64_entails_memRegion _ u0) (pointsTo64_entails_memRegion _ u1))
  have hm2 : memRegion p 20 =
      (∃∗ v0 : BitVec 64, p ↦₆₄ v0) ∗
      (∃∗ v1 : BitVec 64, (p + 8#64) ↦₆₄ v1) ∗
      (∃∗ w1 : BitVec 32, (p + 16#64) ↦₃₂ w1) := by
    rw [memRegion_split p 8 12 (by decide),
      memRegion_split (p + 8#64) 8 4 (by decide),
      ProofLib.memRegion_eight p, ProofLib.memRegion_eight (p + 8#64), memRegion_four (p + 8#64 +
        8#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [hm2] at hm1
  simpa only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc] using hm1

theorem handshakeKeysResultOk104_unpack (p : BitVec 64) (dk : DRKey)
    {rk0 rk1 rk2 rk3 pq0 pq1 pq2 pq3 ck0 ck1 ck2 ck3 : BitVec 64}
    (hrk : ∀ a : BitVec 64, (a ↦ₛ bytesToBv8 dk.rootKey) =
      (a ↦₆₄ rk0) ∗ ((a + 8#64) ↦₆₄ rk1) ∗ ((a + 16#64) ↦₆₄ rk2) ∗ ((a + 24#64) ↦₆₄ rk3))
    (hpq : ∀ a : BitVec 64, (a ↦ₛ bytesToBv8 dk.pqrKey) =
      (a ↦₆₄ pq0) ∗ ((a + 8#64) ↦₆₄ pq1) ∗ ((a + 16#64) ↦₆₄ pq2) ∗ ((a + 24#64) ↦₆₄ pq3))
    (hck : ∀ a : BitVec 64, (a ↦ₛ bytesToBv8 dk.chainKey) =
      (a ↦₆₄ ck0) ∗ ((a + 8#64) ↦₆₄ ck1) ∗ ((a + 16#64) ↦₆₄ ck2) ∗ ((a + 24#64) ↦₆₄ ck3))
    (hrk_len : dk.rootKey.length = 32) (hpq_len : dk.pqrKey.length =
      32) (hck_len : dk.chainKey.length = 32) :
    (p ↦ₛ bytesToBv8 (handshakeKeysResultOk104 dk)) =
      (p ↦₃₂ 0#32) ∗
      ((p + 4#64) ↦₆₄ rk0) ∗ ((p + 12#64) ↦₆₄ rk1) ∗ ((p + 20#64) ↦₆₄ rk2) ∗ ((p + 28#64) ↦₆₄ rk3) ∗
      ((p + 36#64) ↦₆₄ pq0) ∗ ((p + 44#64) ↦₆₄ pq1) ∗ ((p + 52#64) ↦₆₄ pq2) ∗ ((p +
        60#64) ↦₆₄ pq3) ∗
      ((p + 68#64) ↦₆₄ ck0) ∗ ((p + 76#64) ↦₆₄ ck1) ∗ ((p + 84#64) ↦₆₄ ck2) ∗ ((p +
        92#64) ↦₆₄ ck3) ∗
      ((p + 100#64) ↦₃₂ 0#32) := by
  rw [← outPtr_ok104_eq p dk]
  unfold handshakeKeysBytes100 DRKey.ck0
  have h100 :=
    pointsToBytes_100_3blocks_zero (p +
    4#64) dk.rootKey dk.pqrKey dk.chainKey hrk_len hpq_len hck_len
  change (p ↦₃₂ 0#32) ∗ ((p + 4#64) ↦ₛ bytesToBv8 (dk.rootKey ++ dk.pqrKey ++ dk.chainKey ++
    encodeU32LE 0)) = _
  rw [h100, hrk (p + 4#64), hpq (p + 4#64 + 32#64), hck (p + 4#64 + 64#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

set_option maxHeartbeats 8000000



theorem SepWPp.call_inImage_frame' {α : Type} {prog : Program} {img : Obj.Image}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗ ⌜φ⌝ ∗
      T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗
      R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro sf; first | rfl | simp only [Spec.inImage]) :
    SepWPp prog ret s P Q Qp := by
  have hspec' : spec.pre x s = (⌜(img.FrozenLoaded s ∧ s.symtab = img.symtab) ∧ φ⌝ ∗ T) := by
    rw [hspec]
    exact ProofLib.Entails.antisymm
      (Entails.pure_left fun h1 => Entails.pure_left fun h2 => Entails.pure_right ⟨h1, h2⟩ (Entails.refl T))
      (Entails.pure_left fun ⟨h1, h2⟩ => Entails.pure_right h1 (Entails.pure_right h2 (Entails.refl T)))
  refine ProofLib.call_frame_frozen (x := x) (T := T) (F := F)
    hcall hF hsym hpc hrun hsp hlr hspec' ⟨⟨hF, hsym⟩, hφ⟩ hP hexit hpanic
    (fun sf hpcm hrunm hspm hcsm hFm hsymm =>
      hnext sf hpcm hrunm hspm (by simpa [State.spAligned, hspm] using hsp) hcsm hFm hsymm)
    (fun sf R' _ hoom_post => by
      rw [hoom sf] at hoom_post
      exact (not_satisfies_false_sepConj hoom_post).elim)

theorem sepWPp_pure_2 {prog : Program} {ret : BitVec 64} {s : State}
    {A B : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B) Q Qp) :
    SepWPp prog ret s (A ∗ ⌜φ⌝ ∗ B) Q Qp := by
  rw [show A ∗ ⌜φ⌝ ∗ B = ⌜φ⌝ ∗ A ∗ B by ac_rfl]
  exact SepWPp.pure_elim h

theorem cells4_sub768_merge (sp v0 v1 v2 v3 : BitVec 64) :
    ((sp - 768#64) ↦₆₄ v0) ∗ ((sp - 760#64) ↦₆₄ v1) ∗
    ((sp - 752#64) ↦₆₄ v2) ∗ ((sp - 744#64) ↦₆₄ v3) ⊢
    memRegion (sp - 768#64) 32 := by
  rw [(memRegion_cells (sp - 768#64) 4 (by decide) :
    memRegion (sp - 768#64) 32 = cells (sp - 768#64) 4)]
  simp only [cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit', BitVec.reduceSub]
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1
    (Entails.sepExists_right v2 (Entails.sepExists_right v3 (Entails.refl _))))

theorem split_word_0x1000007d0_memRegion (p : BitVec 64) :
    (p ↦₆₄ 0x1000007d0#64) ⊢
      (p ↦₃₂ 0x7d0#32) ∗
      ((p + 4#64) ↦ₛ bytesToBv8 [1]) ∗
      memRegion (p + 5#64) 3 := by
  rw [split_word_0x1000007d0 p]
  exact sepConj_mono_right (sepConj_mono_right (pointsToBytes_entails_memRegion (p + 5#64) [0#8,
    0#8, 0#8]))

structure InitBobCallGhost where
  inp : AcceptKeysInput
  ikBPk : Bytes
  spkBPk : Bytes
  sameAccountByte : BitVec 8
  argPtr : BitVec 64
  pqskPtr : BitVec 64
  ctSlicePtr : BitVec 64
  ctBufPtr : BitVec 64
  ratchetKeyPairPtr : BitVec 64
  outPtr : BitVec 64

def bobParamsFieldsAt (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr : BitVec 64)
    (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes) (sameAccountByte : BitVec 8) : SepProp :=
  (argPtr ↦ₛ bytesToBv8 ikBPk) ∗
  pqxdhAcceptOptFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
  ((argPtr + 297#64) ↦₈ sameAccountByte) ∗
  (ratchetKeyPairPtr ↦ₛ bytesToBv8 spkBPk) ∗
  ((ratchetKeyPairPtr + 32#64) ↦ₛ bytesToBv8 inp.spkBSk)

abbrev initBobErrAt (outPtr : BitVec 64) : SepProp :=
  (outPtr ↦₆₄ 0xffffffffffffffff#64) ∗
  (∃∗ w1 : BitVec 64, ⌜w1 ≠ pollReadyOkWord ∧ w1 ≠ 0xfffffffffffffffd#64⌝ ∗ ((outPtr +
    8#64) ↦₆₄ w1)) ∗
  memRegion (outPtr + 16#64) 328

def initializeBobSessionInnerSpec (P : Primitives) (A : RustAlloc) (img : Obj.Image) :
    Spec InitBobCallGhost where
  pre := fun (g : InitBobCallGhost) s =>
    ⌜s.readReg64 .x0 = g.argPtr ∧
      s.readReg64 .x1 = g.ratchetKeyPairPtr ∧
      s.readReg64 .x8 = g.outPtr ∧
      g.inp.trustedPeer = true ∧
      g.inp.replayOk = true ∧
      g.inp.hdr.opkId?.isSome = g.inp.opkBSk?.isSome ∧
      WellSizedAcceptKeysInput g.inp ∧
      g.ikBPk.length = 32 ∧
      g.spkBPk.length = 32⌝ ∗
    bobParamsFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.ratchetKeyPairPtr
      g.inp g.ikBPk g.spkBPk g.sameAccountByte ∗
    memRegion g.outPtr 344 ∗
    (logFilterAddr img ↦₆₄ 0#64) ∗
    stackAt s.sp (768 + pqxdhEntryStack) ∗
    A.pool
  post := fun (g : InitBobCallGhost) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    bobParamsFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.ratchetKeyPairPtr
      g.inp g.ikBPk g.spkBPk g.sameAccountByte ∗
    (match Model.acceptKeys P g.inp with
     | some drKey =>
       ∃∗ localIkBoxPtr : BitVec 64,
       ∃∗ remoteIkBoxPtr : BitVec 64,
       ∃∗ rootKeyBoxPtr : BitVec 64,
       ∃∗ baseKeyBoxPtr : BitVec 64,
       ∃∗ ratchetPubBoxPtr : BitVec 64,
       ∃∗ ratchetPrivBoxPtr : BitVec 64,
       ∃∗ chainKeyBoxPtr : BitVec 64,
       ∃∗ pad_f4 : BitVec 32,
       ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64, ∃∗
       c4 : BitVec 64,
       ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64,
         ⌜localIkBoxPtr ≠ 0 ∧ remoteIkBoxPtr ≠ 0 ∧ rootKeyBoxPtr ≠ 0 ∧ baseKeyBoxPtr ≠ 0 ∧
           ratchetPubBoxPtr ≠ 0 ∧ ratchetPrivBoxPtr ≠ 0 ∧ chainKeyBoxPtr ≠ 0⌝ ∗
         (localIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC g.ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
         (remoteIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC g.inp.hdr.ikAPk)) ∗
         A.live remoteIkBoxPtr 33 1 ∗
         (rootKeyBoxPtr ↦ₛ bytesToBv8 drKey.rootKey) ∗ A.live rootKeyBoxPtr 32 1 ∗
         (baseKeyBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC g.inp.hdr.ekAPk)) ∗
         A.live baseKeyBoxPtr 33 1 ∗
         (ratchetPubBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC g.spkBPk)) ∗ A.live ratchetPubBoxPtr 33 1 ∗
         (ratchetPrivBoxPtr ↦ₛ bytesToBv8 g.inp.spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
         (chainKeyBoxPtr ↦ₛ bytesToBv8 drKey.chainKey) ∗ A.live chainKeyBoxPtr 32 1 ∗
         (g.outPtr ↦ₛ bobSession344Bv8 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
           0#64 1#64 ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
           pad_f4 c0 c1 c2 c3 c4 d0 d1 d2)
     | none =>
       initBobErrAt g.outPtr ∗
       anyHeap) ∗
    (logFilterAddr img ↦₆₄ 0#64) ∗
    stackAt s0.sp (768 + pqxdhEntryStack) ∗
    A.pool
  onPanic := rustPanicOnOom img

def initializeBobSessionSpec (P : Primitives) (A : RustAlloc) (img : Obj.Image) :
    Spec InitBobCallGhost :=
  (initializeBobSessionInnerSpec P A img).inImage img

theorem stackAt_initBob_entry (sp : BitVec 64) :
    stackAt sp (768 + pqxdhEntryStack) =
      stackAt (sp - 768#64) pqxdhEntryStack ∗
      memRegion (sp - 768#64) 280 ∗
      memRegion (sp - 488#64) 104 ∗
      memRegion (sp - 384#64) 288 ∗
      cells (sp - 96#64) 12 := by
  simp only [stackAt, pqxdhEntryStack]
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 (768 + 16384)) (n := 16384) (k := 768)
      (b' := sp - 768#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 768#64) (n := 280) (k := 488)
      (b' := sp - 488#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 488#64) (n := 104) (k := 384)
      (b' := sp - 384#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 384#64) (n := 288) (k := 96)
      (b' := sp - 96#64) rfl (by bv_omega) (by decide),
    (memRegion_cells (sp - 96#64) 12 (by decide) :
      memRegion (sp - 96#64) 96 = cells (sp - 96#64) 12)]
  have hsub : sp - 768#64 - BitVec.ofNat 64 16384 = sp - BitVec.ofNat 64 (768 + 16384) := by
    bv_omega
  rw [hsub]

theorem memRegion_280_none_split (sp : BitVec 64) :
    memRegion (sp - 768#64) 280 =
      memRegion (sp - 768#64) 4 ∗
      cells (sp - 764#64) 6 ∗
      memRegion (sp - 716#64) 228 := by
  rw [ProofLib.memRegion_split' (b := sp - 768#64) (n := 4) (k := 276)
      (b' := sp - 764#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 764#64) (n := 48) (k := 228)
      (b' := sp - 716#64) rfl (by bv_omega) (by decide),
    (memRegion_cells (sp - 764#64) 6 (by decide) :
      memRegion (sp - 764#64) 48 = cells (sp - 764#64) 6)]

theorem memRegion_88_none_split (sp : BitVec 64) :
    memRegion (sp - 472#64) 88 =
      cells (sp - 472#64) 5 ∗
      memRegion (sp - 432#64) 48 := by
  rw [ProofLib.memRegion_split' (b := sp - 472#64) (n := 40) (k := 48)
      (b' := sp - 432#64) rfl (by bv_omega) (by decide),
    (memRegion_cells (sp - 472#64) 5 (by decide) :
      memRegion (sp - 472#64) 40 = cells (sp - 472#64) 5)]

theorem memRegion_344_none_split (outPtr : BitVec 64) :
    memRegion outPtr 344 =
      cells outPtr 7 ∗
      memRegion (outPtr + 56#64) 288 := by
  rw [ProofLib.memRegion_split' (b := outPtr) (n := 56) (k := 288)
      (b' := outPtr + 56#64) rfl (by bv_omega) (by decide),
    (memRegion_cells outPtr 7 (by decide) :
      memRegion outPtr 56 = cells outPtr 7)]

theorem initBobErrAt_merge (outPtr w1 w2 w3 w4 w5 w6 : BitVec 64)
    (hw1 : w1 ≠ pollReadyOkWord ∧ w1 ≠ 0xfffffffffffffffd#64) :
    (outPtr ↦₆₄ 0xffffffffffffffff#64) ∗
    ((outPtr + 8#64) ↦₆₄ w1) ∗
    ((outPtr + 16#64) ↦₆₄ w2) ∗
    ((outPtr + 24#64) ↦₆₄ w3) ∗
    ((outPtr + 32#64) ↦₆₄ w4) ∗
    ((outPtr + 40#64) ↦₆₄ w5) ∗
    ((outPtr + 48#64) ↦₆₄ w6) ∗
    memRegion (outPtr + 56#64) 288 ⊢
    initBobErrAt outPtr := by
  unfold initBobErrAt
  refine sepConj_mono_right ?_
  have hw1_ent : ((outPtr + 8#64) ↦₆₄ w1) ⊢
      ∃∗ w1' : BitVec 64, ⌜w1' ≠ pollReadyOkWord ∧ w1' ≠ 0xfffffffffffffffd#64⌝ ∗ ((outPtr +
        8#64) ↦₆₄ w1') := by
    rw [← pure_sepConj_of_true hw1 ((outPtr + 8#64) ↦₆₄ w1)]
    exact Entails.sepExists_right w1 (Entails.refl _)
  have hc5 : ((outPtr + 16#64) ↦₆₄ w2) ∗ ((outPtr + 24#64) ↦₆₄ w3) ∗
      ((outPtr + 32#64) ↦₆₄ w4) ∗ ((outPtr + 40#64) ↦₆₄ w5) ∗ ((outPtr + 48#64) ↦₆₄ w6) ⊢
      memRegion (outPtr + 16#64) 40 := by
    rw [(memRegion_cells (outPtr + 16#64) 5 (by decide) :
      memRegion (outPtr + 16#64) 40 = cells (outPtr + 16#64) 5)]
    simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.sepExists_right w2 (Entails.sepExists_right w3
      (Entails.sepExists_right w4 (Entails.sepExists_right w5 (Entails.sepExists_right w6
        (Entails.refl _)))))
  have hm328 : memRegion (outPtr + 16#64) 40 ∗ memRegion (outPtr + 56#64) 288 =
      memRegion (outPtr + 16#64) 328 := by
    rw [show outPtr + 56#64 = outPtr + 16#64 + BitVec.ofNat 64 40 by bv_omega,
        ← memRegion_split (outPtr + 16#64) 40 288 (by decide)]
  rw [← hm328]
  have hrearr :
      ((outPtr + 8#64) ↦₆₄ w1) ∗ (((outPtr + 16#64) ↦₆₄ w2) ∗ (((outPtr + 24#64) ↦₆₄ w3) ∗
        (((outPtr + 32#64) ↦₆₄ w4) ∗ (((outPtr + 40#64) ↦₆₄ w5) ∗ (((outPtr + 48#64) ↦₆₄ w6) ∗
          memRegion (outPtr + 56#64) 288))))) =
      ((outPtr + 8#64) ↦₆₄ w1) ∗ ((((outPtr + 16#64) ↦₆₄ w2) ∗ (((outPtr + 24#64) ↦₆₄ w3) ∗
        (((outPtr + 32#64) ↦₆₄ w4) ∗ (((outPtr + 40#64) ↦₆₄ w5) ∗ ((outPtr + 48#64) ↦₆₄ w6))))) ∗
          memRegion (outPtr + 56#64) 288) := by ac_rfl
  rw [hrearr]
  exact sepConj_mono hw1_ent (sepConj_mono_left hc5)


theorem cells6_sub764_merge (sp v0 v1 v2 v3 v4 v5 : BitVec 64) :
    ((sp - 764#64) ↦₆₄ v0) ∗ ((sp - 756#64) ↦₆₄ v1) ∗ ((sp - 748#64) ↦₆₄ v2) ∗
    ((sp - 740#64) ↦₆₄ v3) ∗ ((sp - 732#64) ↦₆₄ v4) ∗ ((sp - 724#64) ↦₆₄ v5) ⊢
    cells (sp - 764#64) 6 := by
  simp only [cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit', BitVec.reduceSub]
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
    (Entails.sepExists_right v3 (Entails.sepExists_right v4 (Entails.sepExists_right v5
      (Entails.refl _))))))

theorem sub488_none_104_merge (sp w1 w2 w3 w4 w5 w6 : BitVec 64) :
    ((sp - 488#64) ↦₃₂ 1#32) ∗
    memRegion (sp - 484#64) 4 ∗
    ((sp - 480#64) ↦₆₄ w1) ∗
    ((sp - 472#64) ↦₆₄ w2) ∗
    ((sp - 464#64) ↦₆₄ w3) ∗
    ((sp - 456#64) ↦₆₄ w4) ∗
    ((sp - 448#64) ↦₆₄ w5) ∗
    ((sp - 440#64) ↦₆₄ w6) ∗
    memRegion (sp - 432#64) 48 ⊢
    memRegion (sp - 488#64) 104 := by
  rw [ProofLib.memRegion_split' (b := sp - 488#64) (n := 4) (k := 100)
      (b' := sp - 484#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 484#64) (n := 4) (k := 96)
      (b' := sp - 480#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 480#64) (n := 48) (k := 48)
      (b' := sp - 432#64) rfl (by bv_omega) (by decide),
    (memRegion_cells (sp - 480#64) 6 (by decide) :
      memRegion (sp - 480#64) 48 = cells (sp - 480#64) 6)]
  have hc6 :
      ((sp - 480#64) ↦₆₄ w1) ∗ (((sp - 472#64) ↦₆₄ w2) ∗ (((sp - 464#64) ↦₆₄ w3) ∗
        (((sp - 456#64) ↦₆₄ w4) ∗ (((sp - 448#64) ↦₆₄ w5) ∗ ((sp - 440#64) ↦₆₄ w6))))) ⊢
      cells (sp - 480#64) 6 := by
    simp only [cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit', BitVec.reduceSub]
    exact Entails.sepExists_right w1 (Entails.sepExists_right w2 (Entails.sepExists_right w3
      (Entails.sepExists_right w4 (Entails.sepExists_right w5 (Entails.sepExists_right w6
        (Entails.refl _))))))
  have hrearr :
      ((sp - 488#64) ↦₃₂ 1#32) ∗ (memRegion (sp - 484#64) 4 ∗ (((sp - 480#64) ↦₆₄ w1) ∗
        (((sp - 472#64) ↦₆₄ w2) ∗ (((sp - 464#64) ↦₆₄ w3) ∗ (((sp - 456#64) ↦₆₄ w4) ∗
          (((sp - 448#64) ↦₆₄ w5) ∗ (((sp - 440#64) ↦₆₄ w6) ∗ memRegion (sp - 432#64) 48))))))) =
      ((sp - 488#64) ↦₃₂ 1#32) ∗ (memRegion (sp - 484#64) 4 ∗
        ((((sp - 480#64) ↦₆₄ w1) ∗ (((sp - 472#64) ↦₆₄ w2) ∗ (((sp - 464#64) ↦₆₄ w3) ∗
          (((sp - 456#64) ↦₆₄ w4) ∗ (((sp - 448#64) ↦₆₄ w5) ∗ ((sp - 440#64) ↦₆₄ w6)))))) ∗
        memRegion (sp - 432#64) 48)) := by ac_rfl
  rw [hrearr]
  exact sepConj_mono (pointsTo32_entails_memRegion _ 1#32)
    (sepConj_mono_right (sepConj_mono_left hc6))

theorem cells12_sub96_merge (sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : BitVec 64) :
    ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗ ((sp - 80#64) ↦₆₄ v2) ∗ ((sp - 72#64) ↦₆₄ v3) ∗
    ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗ ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗
    ((sp - 32#64) ↦₆₄ v8) ∗ ((sp - 24#64) ↦₆₄ v9) ∗ ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11) ⊢
    cells (sp - 96#64) 12 := by
  simp only [cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit', BitVec.reduceSub]
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
    (Entails.sepExists_right v3 (Entails.sepExists_right v4 (Entails.sepExists_right v5
      (Entails.sepExists_right v6 (Entails.sepExists_right v7 (Entails.sepExists_right v8
        (Entails.sepExists_right v9 (Entails.sepExists_right v10 (Entails.sepExists_right v11
        (Entails.refl _))))))))))))



theorem memRegion_280_some_split (sp : BitVec 64) :
    memRegion (sp - 768#64) 280 =
      cells (sp - 768#64) 12 ∗
      (∃∗ w672 : BitVec 32, (sp - 672#64) ↦₃₂ w672) ∗
      memRegion (sp - 668#64) 12 ∗
      cells (sp - 656#64) 8 ∗
      (∃∗ w592 : BitVec 32, (sp - 592#64) ↦₃₂ w592) ∗
      memRegion (sp - 588#64) 12 ∗
      cells (sp - 576#64) 4 ∗
      memRegion (sp - 544#64) 56 := by
  rw [ProofLib.memRegion_split' (b := sp - 768#64) (n := 96) (k := 184)
      (b' := sp - 672#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 672#64) (n := 4) (k := 180)
      (b' := sp - 668#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 668#64) (n := 12) (k := 168)
      (b' := sp - 656#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 656#64) (n := 64) (k := 104)
      (b' := sp - 592#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 592#64) (n := 4) (k := 100)
      (b' := sp - 588#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 588#64) (n := 12) (k := 88)
      (b' := sp - 576#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 576#64) (n := 32) (k := 56)
      (b' := sp - 544#64) rfl (by bv_omega) (by decide),
    (memRegion_cells (sp - 768#64) 12 (by decide) :
      memRegion (sp - 768#64) 96 = cells (sp - 768#64) 12),
    memRegion_four (sp - 672#64),
    (memRegion_cells (sp - 656#64) 8 (by decide) :
      memRegion (sp - 656#64) 64 = cells (sp - 656#64) 8),
    memRegion_four (sp - 592#64),
    (memRegion_cells (sp - 576#64) 4 (by decide) :
      memRegion (sp - 576#64) 32 = cells (sp - 576#64) 4)]

private theorem cond_ne_subs32_1_1 :
    ConditionHolds CondCode.NE (subsPState32 1#32 1#32) = false := by
  simp only [ConditionHolds, subsPState32]; decide

@[local simp, wp_norm, arm64_norm]
private theorem cond_ne_subs32_0_1 :
    ConditionHolds CondCode.NE (subsPState32 0#32 1#32) = true := by
  simp only [ConditionHolds, subsPState32]; decide

@[local simp, wp_norm, arm64_norm]
private theorem cond_ne_subs64_0_1 :
    ConditionHolds CondCode.NE (subsPState64 0#64 1#64) = true := by
  simp only [ConditionHolds, subsPState64]; decide



theorem stackAt_entry_some_split (sp : BitVec 64) :
    stackAt sp pqxdhEntryStack =
      memRegion (sp - 16384#64) 12128 ∗
      memRegion (sp - 4256#64) 128 ∗
      memRegion (sp - 4128#64) 32 ∗
      stackAt sp allocHookStack := by
  simp only [stackAt, pqxdhEntryStack, allocHookStack]
  rw [ProofLib.memRegion_split' (b := sp - 16384#64) (n := 12128) (k := 4256)
      (b' := sp - 4256#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 4256#64) (n := 128) (k := 4128)
      (b' := sp - 4128#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 4128#64) (n := 32) (k := 4096)
      (b' := sp - 4096#64) rfl (by bv_omega) (by decide)]

theorem memRegion_160_withSenderChain (sp : BitVec 64) :
    memRegion (sp - 4256#64) 128 ∗ memRegion (sp - 4128#64) 32 =
      memRegion (sp - 4256#64) 160 := by
  exact (ProofLib.memRegion_split' (b := sp - 4256#64) (n := 128) (k := 32)
    (b' := sp - 4128#64) rfl (by bv_omega) (by decide)).symm

theorem sub488_to_sessionState_frame (sp : BitVec 64)
    (v488 v480 v460 pq0 pq1 pq2 pq3 ck0 ck1 ck2 ck3 : BitVec 64)
    (v472 v468 v388 : BitVec 32) :
    ((sp - 488#64) ↦₆₄ v488) ∗
    ((sp - 480#64) ↦₆₄ v480) ∗
    ((sp - 472#64) ↦₃₂ v472) ∗
    ((sp - 468#64) ↦₃₂ v468) ∗
    ((sp - 464#64) ↦ₛ bytesToBv8 [1]) ∗
    memRegion (sp - 463#64) 3 ∗
    ((sp - 460#64) ↦₆₄ v460) ∗
    ((sp - 452#64) ↦₆₄ pq0) ∗ ((sp - 444#64) ↦₆₄ pq1) ∗ ((sp - 436#64) ↦₆₄ pq2) ∗ ((sp -
      428#64) ↦₆₄ pq3) ∗
    ((sp - 420#64) ↦₆₄ ck0) ∗ ((sp - 412#64) ↦₆₄ ck1) ∗ ((sp - 404#64) ↦₆₄ ck2) ∗ ((sp -
      396#64) ↦₆₄ ck3) ∗
    ((sp - 388#64) ↦₃₂ v388) ∗
    memRegion (sp - 384#64) 288 ⊢
    cells (sp - 488#64) 19 ∗
    memRegion (sp - 336#64) 92 ∗
    (∃∗ pad_f4 : BitVec 32, (sp - 244#64) ↦₃₂ pad_f4) ∗
    memRegion (sp - 240#64) 96 ∗
    memRegion (sp - 144#64) 48 := by
  have h104 :
      ((sp - 488#64) ↦₆₄ v488) ∗
      ((sp - 480#64) ↦₆₄ v480) ∗
      ((sp - 472#64) ↦₃₂ v472) ∗
      ((sp - 468#64) ↦₃₂ v468) ∗
      ((sp - 464#64) ↦ₛ bytesToBv8 [1]) ∗
      memRegion (sp - 463#64) 3 ∗
      ((sp - 460#64) ↦₆₄ v460) ∗
      ((sp - 452#64) ↦₆₄ pq0) ∗ ((sp - 444#64) ↦₆₄ pq1) ∗ ((sp - 436#64) ↦₆₄ pq2) ∗ ((sp -
        428#64) ↦₆₄ pq3) ∗
      ((sp - 420#64) ↦₆₄ ck0) ∗ ((sp - 412#64) ↦₆₄ ck1) ∗ ((sp - 404#64) ↦₆₄ ck2) ∗ ((sp -
        396#64) ↦₆₄ ck3) ∗
      ((sp - 388#64) ↦₃₂ v388) ⊢
      memRegion (sp - 488#64) 104 := by
    rw [ProofLib.memRegion_split' (b := sp - 488#64) (n := 8) (k := 96) (b' :=
      sp - 480#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 480#64) (n := 8) (k := 88) (b' :=
        sp - 472#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 472#64) (n := 4) (k := 84) (b' :=
        sp - 468#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 468#64) (n := 4) (k := 80) (b' :=
        sp - 464#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 464#64) (n := 1) (k := 79) (b' :=
        sp - 463#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 463#64) (n := 3) (k := 76) (b' :=
        sp - 460#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 460#64) (n := 8) (k := 68) (b' :=
        sp - 452#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 452#64) (n := 8) (k := 60) (b' :=
        sp - 444#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 444#64) (n := 8) (k := 52) (b' :=
        sp - 436#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 436#64) (n := 8) (k := 44) (b' :=
        sp - 428#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 428#64) (n := 8) (k := 36) (b' :=
        sp - 420#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 420#64) (n := 8) (k := 28) (b' :=
        sp - 412#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 412#64) (n := 8) (k := 20) (b' :=
        sp - 404#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 404#64) (n := 8) (k := 12) (b' :=
        sp - 396#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 396#64) (n := 8) (k := 4) (b' :=
        sp - 388#64) rfl (by bv_omega) (by decide)]
    have hb1 : ((sp - 464#64) ↦ₛ bytesToBv8 [1]) ⊢ memRegion (sp - 464#64) 1 := by
      exact pointsToBytes_entails_memRegion (sp - 464#64) (bytesToBv8 [1])
    exact sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo32_entails_memRegion _ _)
          (sepConj_mono (pointsTo32_entails_memRegion _ _)
            (sepConj_mono hb1
              (sepConj_mono (Entails.refl _)
                (sepConj_mono (pointsTo64_entails_memRegion _ _)
                  (sepConj_mono (pointsTo64_entails_memRegion _ _)
                    (sepConj_mono (pointsTo64_entails_memRegion _ _)
                      (sepConj_mono (pointsTo64_entails_memRegion _ _)
                        (sepConj_mono (pointsTo64_entails_memRegion _ _)
                          (sepConj_mono (pointsTo64_entails_memRegion _ _)
                            (sepConj_mono (pointsTo64_entails_memRegion _ _)
                              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                                (sepConj_mono (pointsTo64_entails_memRegion _ _)
                                  (pointsTo32_entails_memRegion _ _)))))))))))))))
  have hm392 :
      memRegion (sp - 488#64) 104 ∗ memRegion (sp - 384#64) 288 =
      cells (sp - 488#64) 19 ∗
      memRegion (sp - 336#64) 92 ∗
      (∃∗ pad_f4 : BitVec 32, (sp - 244#64) ↦₃₂ pad_f4) ∗
      memRegion (sp - 240#64) 96 ∗
      memRegion (sp - 144#64) 48 := by
    rw [(ProofLib.memRegion_split' (b := sp - 488#64) (n := 104) (k := 288)
        (b' := sp - 384#64) rfl (by bv_omega) (by decide)).symm,
      ProofLib.memRegion_split' (b := sp - 488#64) (n := 152) (k := 240)
        (b' := sp - 336#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 336#64) (n := 92) (k := 148)
        (b' := sp - 244#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 244#64) (n := 4) (k := 144)
        (b' := sp - 240#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 240#64) (n := 96) (k := 48)
        (b' := sp - 144#64) rfl (by bv_omega) (by decide),
      (memRegion_cells (sp - 488#64) 19 (by decide) :
        memRegion (sp - 488#64) 152 = cells (sp - 488#64) 19),
      memRegion_four (sp - 244#64)]
  rw [← hm392]
  have hrearr :
      ((sp - 488#64) ↦₆₄ v488) ∗ (((sp - 480#64) ↦₆₄ v480) ∗ (((sp - 472#64) ↦₃₂ v472) ∗
        (((sp - 468#64) ↦₃₂ v468) ∗ (((sp - 464#64) ↦ₛ bytesToBv8 [1]) ∗ (memRegion (sp -
        463#64) 3 ∗
          (((sp - 460#64) ↦₆₄ v460) ∗ (((sp - 452#64) ↦₆₄ pq0) ∗ (((sp - 444#64) ↦₆₄ pq1) ∗
            (((sp - 436#64) ↦₆₄ pq2) ∗ (((sp - 428#64) ↦₆₄ pq3) ∗ (((sp - 420#64) ↦₆₄ ck0) ∗
              (((sp - 412#64) ↦₆₄ ck1) ∗ (((sp - 404#64) ↦₆₄ ck2) ∗ (((sp - 396#64) ↦₆₄ ck3) ∗
                (((sp - 388#64) ↦₃₂ v388) ∗ memRegion (sp - 384#64) 288))))))))))))))) =
      (((sp - 488#64) ↦₆₄ v488) ∗ (((sp - 480#64) ↦₆₄ v480) ∗ (((sp - 472#64) ↦₃₂ v472) ∗
        (((sp - 468#64) ↦₃₂ v468) ∗ (((sp - 464#64) ↦ₛ bytesToBv8 [1]) ∗ (memRegion (sp -
        463#64) 3 ∗
          (((sp - 460#64) ↦₆₄ v460) ∗ (((sp - 452#64) ↦₆₄ pq0) ∗ (((sp - 444#64) ↦₆₄ pq1) ∗
            (((sp - 436#64) ↦₆₄ pq2) ∗ (((sp - 428#64) ↦₆₄ pq3) ∗ (((sp - 420#64) ↦₆₄ ck0) ∗
              (((sp - 412#64) ↦₆₄ ck1) ∗ (((sp - 404#64) ↦₆₄ ck2) ∗ (((sp - 396#64) ↦₆₄ ck3) ∗
                ((sp - 388#64) ↦₃₂ v388)))))))))))))))) ∗ memRegion (sp - 384#64) 288 := by ac_rfl
  rw [hrearr]
  exact sepConj_mono_left h104


theorem post100_pack (ptr : BitVec 64) (pad_f4 : BitVec 32)
    (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) :
    ((ptr + 0xf4#64) ↦₃₂ pad_f4) ∗
    ((ptr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗
    ((ptr + 0x100#64) ↦₆₄ c0) ∗
    ((ptr + 0x108#64) ↦₆₄ c1) ∗
    ((ptr + 0x110#64) ↦₆₄ c2) ∗
    ((ptr + 0x118#64) ↦₆₄ c3) ∗
    ((ptr + 0x120#64) ↦₆₄ c4) ∗
    ((ptr + 0x128#64) ↦₆₄ 0xffffffffffffffff#64) ∗
    ((ptr + 0x130#64) ↦₆₄ d0) ∗
    ((ptr + 0x138#64) ↦₆₄ d1) ∗
    ((ptr + 0x140#64) ↦₆₄ d2) ∗
    ((ptr + 0x148#64) ↦₆₄ 4#64) ∗
    ((ptr + 0x150#64) ↦₆₄ 0#64) =
      ((ptr + 0xf4#64) ↦ₛ (unpack32 pad_f4 ++ bobTail96Bv8 c0 c1 c2 c3 c4 d0 d1 d2)) := by
  have h96 := bobTail96_eq_pointsToBytes ptr c0 c1 c2 c3 c4 d0 d1 d2
  rw [pointsToBytes_append (ptr + 0xf4#64) (unpack32 pad_f4),
      unpack32_length,
      show ptr + 0xf4#64 + BitVec.ofNat 64 4 = ptr + 0xf8#64 by bv_omega,
      ← pointsTo32_eq_pointsToBytes (ptr + 0xf4#64) pad_f4,
      ← h96]

def pqxdhAcceptRestAt (basePtr pqskPtr ctSlicePtr ctBufPtr : BitVec 64) (inp : AcceptKeysInput) :
    SepProp :=
  ((basePtr + 32#64) ↦ₛ bytesToBv8 inp.ikBSk) ∗
  ((basePtr + 96#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
  ((basePtr + 208#64) ↦₆₄ pqskPtr) ∗
  ((basePtr + 216#64) ↦₆₄ 3168#64) ∗
  ((basePtr + 224#64) ↦₆₄ ctSlicePtr) ∗
  ((basePtr + 232#64) ↦₈ (if (match inp.opkBSk? with
    | some _ => true | none => false) = true then 1#8 else 0#8)) ∗
  (match inp.opkBSk? with | some opkSk => (basePtr + 265#64) ↦ₛ bytesToBv8 opkSk | none => .emp) ∗
  (pqskPtr ↦₈ (bytesToBv8 inp.pqspkBSk).getD 0 0#8) ∗
  ((pqskPtr + 1#64) ↦ₛ (bytesToBv8 inp.pqspkBSk).drop 1) ∗
  (ctSlicePtr ↦₆₄ ctBufPtr) ∗
  ((ctSlicePtr + 8#64) ↦₆₄ 1569#64) ∗
  (ctBufPtr ↦₈ 8#8) ∗
  ((ctBufPtr + 1#64) ↦₈ (bytesToBv8 inp.hdr.kemCt).getD 0 0#8) ∗
  ((ctBufPtr + 2#64) ↦ₛ (bytesToBv8 inp.hdr.kemCt).drop 1)

theorem pqxdhAcceptFieldsAt_split (basePtr pqskPtr ctSlicePtr ctBufPtr : BitVec 64) (inp :
    AcceptKeysInput) :
    pqxdhAcceptOptFieldsAt basePtr pqskPtr ctSlicePtr ctBufPtr inp =
      ((basePtr + 128#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
      ((basePtr + 160#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
      pqxdhAcceptRestAt basePtr pqskPtr ctSlicePtr ctBufPtr inp := by
  unfold pqxdhAcceptOptFieldsAt pqxdhAcceptRestAt
  ac_rfl

theorem bobSession344_pack (ptr localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap
    spqrBufPtr
    ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) :
    (ptr ↦ₛ bobHead144Bv8 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap
      spqrBufPtr) ∗
    senderChainFieldsAt ptr ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr 0#32 ∗
    ((ptr + 0xf4#64) ↦ₛ (unpack32 pad_f4 ++ bobTail96Bv8 c0 c1 c2 c3 c4 d0 d1 d2)) =
      (ptr ↦ₛ bobSession344Bv8 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap
        spqrBufPtr
        ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) := by
  unfold bobSession344Bv8
  rw [senderChainFieldsAt_eq_pointsToBytes]
  simp only [List.append_assoc, pointsToBytes_append, bobHead144Bv8_length,
    senderChainBytes100_length,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_160_sub5024 (sp : BitVec 64) :
    memRegion (sp - 5024#64) 128 ∗ memRegion (sp - 4896#64) 32 =
      memRegion (sp - 5024#64) 160 := by
  exact (ProofLib.memRegion_split' (b := sp - 5024#64) (n := 128) (k := 32)
    (b' := sp - 4896#64) rfl (by bv_omega) (by decide)).symm

theorem stackAt_entry_some_merge (sp : BitVec 64) :
    memRegion (sp - 17152#64) 12128 ∗
    memRegion (sp - 5024#64) 160 ∗
    stackAt (sp - 768#64) allocHookStack =
      stackAt (sp - 768#64) pqxdhEntryStack := by
  have h := stackAt_entry_some_split (sp - 768#64)
  simp only [BitVec.sub_sub, BitVec.reduceAdd] at h
  rw [← memRegion_160_sub5024 sp, h]
  ac_rfl

theorem sub488_some_post_merge (sp : BitVec 64) (bs344 : List (BitVec 8)) (h344 : bs344.length =
    344) :
    ((sp - 488#64) ↦ₛ bs344) ∗ memRegion (sp - 144#64) 48 ⊢
      memRegion (sp - 488#64) 104 ∗ memRegion (sp - 384#64) 288 := by
  have hm344 : ((sp - 488#64) ↦ₛ bs344) ⊢ memRegion (sp - 488#64) 344 := by
    rw [← h344]; exact pointsToBytes_entails_memRegion (sp - 488#64) bs344
  have hsplit :
      memRegion (sp - 488#64) 344 ∗ memRegion (sp - 144#64) 48 =
      memRegion (sp - 488#64) 104 ∗ memRegion (sp - 384#64) 288 := by
    rw [(ProofLib.memRegion_split' (b := sp - 488#64) (n := 344) (k := 48)
        (b' := sp - 144#64) rfl (by bv_omega) (by decide)).symm,
      ProofLib.memRegion_split' (b := sp - 488#64) (n := 104) (k := 288)
        (b' := sp - 384#64) rfl (by bv_omega) (by decide)]
  rw [← hsplit]
  exact sepConj_mono_left hm344

theorem sub768_some_post_merge (sp : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : BitVec 64)
    (u0 u1 u2 u3 u4 u5 u6 u7 : BitVec 64)
    (q0 q1 q2 q3 : BitVec 64)
    (w672 w592 : BitVec 32) :
    ((sp - 768#64) ↦₆₄ v0) ∗ ((sp - 760#64) ↦₆₄ v1) ∗ ((sp - 752#64) ↦₆₄ v2) ∗ ((sp -
      744#64) ↦₆₄ v3) ∗
    ((sp - 736#64) ↦₆₄ v4) ∗ ((sp - 728#64) ↦₆₄ v5) ∗ ((sp - 720#64) ↦₆₄ v6) ∗ ((sp -
      712#64) ↦₆₄ v7) ∗
    ((sp - 704#64) ↦₆₄ v8) ∗ ((sp - 696#64) ↦₆₄ v9) ∗ ((sp - 688#64) ↦₆₄ v10) ∗ ((sp -
      680#64) ↦₆₄ v11) ∗
    ((sp - 672#64) ↦₃₂ w672) ∗
    memRegion (sp - 668#64) 12 ∗
    ((sp - 656#64) ↦₆₄ u0) ∗ ((sp - 648#64) ↦₆₄ u1) ∗ ((sp - 640#64) ↦₆₄ u2) ∗ ((sp -
      632#64) ↦₆₄ u3) ∗
    ((sp - 624#64) ↦₆₄ u4) ∗ ((sp - 616#64) ↦₆₄ u5) ∗ ((sp - 608#64) ↦₆₄ u6) ∗ ((sp -
      600#64) ↦₆₄ u7) ∗
    ((sp - 592#64) ↦₃₂ w592) ∗
    memRegion (sp - 588#64) 12 ∗
    ((sp - 576#64) ↦₆₄ q0) ∗ ((sp - 568#64) ↦₆₄ q1) ∗ ((sp - 560#64) ↦₆₄ q2) ∗ ((sp -
      552#64) ↦₆₄ q3) ∗
    memRegion (sp - 544#64) 56 ⊢
    memRegion (sp - 768#64) 280 := by
  rw [memRegion_280_some_split sp]
  have hc12 :
      ((sp - 768#64) ↦₆₄ v0) ∗ (((sp - 760#64) ↦₆₄ v1) ∗ (((sp - 752#64) ↦₆₄ v2) ∗ (((sp -
        744#64) ↦₆₄ v3) ∗
        (((sp - 736#64) ↦₆₄ v4) ∗ (((sp - 728#64) ↦₆₄ v5) ∗ (((sp - 720#64) ↦₆₄ v6) ∗ (((sp -
        712#64) ↦₆₄ v7) ∗
          (((sp - 704#64) ↦₆₄ v8) ∗ (((sp - 696#64) ↦₆₄ v9) ∗ (((sp - 688#64) ↦₆₄ v10) ∗ ((sp -
          680#64) ↦₆₄ v11))))))))))) ⊢
      cells (sp - 768#64) 12 := by
    simp only [cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit', BitVec.reduceSub]
    exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
      (Entails.sepExists_right v3 (Entails.sepExists_right v4 (Entails.sepExists_right v5
        (Entails.sepExists_right v6 (Entails.sepExists_right v7 (Entails.sepExists_right v8
          (Entails.sepExists_right v9 (Entails.sepExists_right v10 (Entails.sepExists_right v11
          (Entails.refl _))))))))))))
  have hc8 :
      ((sp - 656#64) ↦₆₄ u0) ∗ (((sp - 648#64) ↦₆₄ u1) ∗ (((sp - 640#64) ↦₆₄ u2) ∗ (((sp -
        632#64) ↦₆₄ u3) ∗
        (((sp - 624#64) ↦₆₄ u4) ∗ (((sp - 616#64) ↦₆₄ u5) ∗ (((sp - 608#64) ↦₆₄ u6) ∗ ((sp -
        600#64) ↦₆₄ u7))))))) ⊢
      cells (sp - 656#64) 8 := by
    simp only [cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit', BitVec.reduceSub]
    exact Entails.sepExists_right u0 (Entails.sepExists_right u1 (Entails.sepExists_right u2
      (Entails.sepExists_right u3 (Entails.sepExists_right u4 (Entails.sepExists_right u5
        (Entails.sepExists_right u6 (Entails.sepExists_right u7 (Entails.refl _))))))))
  have hc4 :
      ((sp - 576#64) ↦₆₄ q0) ∗ (((sp - 568#64) ↦₆₄ q1) ∗ (((sp - 560#64) ↦₆₄ q2) ∗ ((sp -
        552#64) ↦₆₄ q3))) ⊢
      cells (sp - 576#64) 4 := by
    simp only [cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit', BitVec.reduceSub]
    exact Entails.sepExists_right q0 (Entails.sepExists_right q1
      (Entails.sepExists_right q2 (Entails.sepExists_right q3 (Entails.refl _))))
  have hw1 : ((sp - 672#64) ↦₃₂ w672) ⊢ ∃∗ w : BitVec 32, (sp - 672#64) ↦₃₂ w :=
    Entails.sepExists_right w672 (Entails.refl _)
  have hw2 : ((sp - 592#64) ↦₃₂ w592) ⊢ ∃∗ w : BitVec 32, (sp - 592#64) ↦₃₂ w :=
    Entails.sepExists_right w592 (Entails.refl _)
  have hrearr :
      ((sp - 768#64) ↦₆₄ v0) ∗ (((sp - 760#64) ↦₆₄ v1) ∗ (((sp - 752#64) ↦₆₄ v2) ∗ (((sp -
        744#64) ↦₆₄ v3) ∗
        (((sp - 736#64) ↦₆₄ v4) ∗ (((sp - 728#64) ↦₆₄ v5) ∗ (((sp - 720#64) ↦₆₄ v6) ∗ (((sp -
        712#64) ↦₆₄ v7) ∗
          (((sp - 704#64) ↦₆₄ v8) ∗ (((sp - 696#64) ↦₆₄ v9) ∗ (((sp - 688#64) ↦₆₄ v10) ∗ (((sp -
          680#64) ↦₆₄ v11) ∗
            (((sp - 672#64) ↦₃₂ w672) ∗ (memRegion (sp - 668#64) 12 ∗
              (((sp - 656#64) ↦₆₄ u0) ∗ (((sp - 648#64) ↦₆₄ u1) ∗ (((sp - 640#64) ↦₆₄ u2) ∗ (((sp -
              632#64) ↦₆₄ u3) ∗
                (((sp - 624#64) ↦₆₄ u4) ∗ (((sp - 616#64) ↦₆₄ u5) ∗ (((sp - 608#64) ↦₆₄ u6) ∗
                (((sp - 600#64) ↦₆₄ u7) ∗
                  (((sp - 592#64) ↦₃₂ w592) ∗ (memRegion (sp - 588#64) 12 ∗
                    (((sp - 576#64) ↦₆₄ q0) ∗ (((sp - 568#64) ↦₆₄ q1) ∗ (((sp - 560#64) ↦₆₄ q2) ∗
                    (((sp - 552#64) ↦₆₄ q3) ∗
                      memRegion (sp - 544#64) 56))))))))))))))))))))))))))) =
      (((sp - 768#64) ↦₆₄ v0) ∗ (((sp - 760#64) ↦₆₄ v1) ∗ (((sp - 752#64) ↦₆₄ v2) ∗ (((sp -
        744#64) ↦₆₄ v3) ∗
        (((sp - 736#64) ↦₆₄ v4) ∗ (((sp - 728#64) ↦₆₄ v5) ∗ (((sp - 720#64) ↦₆₄ v6) ∗ (((sp -
        712#64) ↦₆₄ v7) ∗
          (((sp - 704#64) ↦₆₄ v8) ∗ (((sp - 696#64) ↦₆₄ v9) ∗ (((sp - 688#64) ↦₆₄ v10) ∗ ((sp -
          680#64) ↦₆₄ v11)))))))))))) ∗
      (((sp - 672#64) ↦₃₂ w672) ∗ (memRegion (sp - 668#64) 12 ∗
        ((((sp - 656#64) ↦₆₄ u0) ∗ (((sp - 648#64) ↦₆₄ u1) ∗ (((sp - 640#64) ↦₆₄ u2) ∗ (((sp -
        632#64) ↦₆₄ u3) ∗
          (((sp - 624#64) ↦₆₄ u4) ∗ (((sp - 616#64) ↦₆₄ u5) ∗ (((sp - 608#64) ↦₆₄ u6) ∗ ((sp -
          600#64) ↦₆₄ u7)))))))) ∗
          (((sp - 592#64) ↦₃₂ w592) ∗ (memRegion (sp - 588#64) 12 ∗
            ((((sp - 576#64) ↦₆₄ q0) ∗ (((sp - 568#64) ↦₆₄ q1) ∗ (((sp - 560#64) ↦₆₄ q2) ∗ ((sp -
            552#64) ↦₆₄ q3)))) ∗
              memRegion (sp - 544#64) 56)))))) := by ac_rfl
  rw [hrearr]
  exact sepConj_mono hc12 (sepConj_mono hw1 (sepConj_mono_right (sepConj_mono hc8
    (sepConj_mono hw2 (sepConj_mono_right (sepConj_mono_left hc4))))))


attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  CryptoVerification.libsignalSessionCode_fnOff_0x21c80

end CryptoVerification.E2E.Pqxdh.ResponderCore
