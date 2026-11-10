/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewEncodeTags123
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.TripleRatchet.Wire.NewEncodeTags456
import LibsignalBinary.Proofs.TripleRatchet.Wire.NewMacAndBoxes
import ProofLib.SepLogic.WPp

/-!
# `<libsignal_protocol::protocol::SignalMessage>::new` (`0x1d918`)

Top-level subroutine correctness proof composing the prologue and input copies (`+0x000 → +0x100`),
`wire::SignalMessage` construction and tags 1–3 encoding (`+0x100 → +0x278`), tags 4–6 encoding
(`+0x278 → +0x3dc`), and MAC computation, `sret` packing, and temporary deallocation (`+0x3dc → ret`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet.Prost
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm]
  sp_sub_96_sub_56 sp_sub_96_sub_64 sp_sub_96_sub_72 sp_sub_96_sub_80
  bv_add_8_sub_self add_one_eq_zero_iff_noneCap add_one_beq_zero_iff_noneCap
  add_one_bne_zero_iff_ne_noneCap

/-! ## Separation-logic glue between segments -/

theorem optPqBuf_extract_pin (A : RustAlloc) (cap ptr : BitVec 64) (pq : List (BitVec 8)) :
    optPqBuf A cap ptr pq ⊢ ⌜PqPinOk cap ptr pq⌝ ∗ optPqBuf A cap ptr pq := by
  unfold optPqBuf PqPinOk; by_cases h : pq.isEmpty
  · simp only [h, ↓reduceIte]; exact Entails.pure_left fun hc => Entails.pure_right hc (Entails.pure_right hc (Entails.refl _))
  · simp only [h, Bool.false_eq_true, ↓reduceIte]; exact Entails.pure_left fun hp => Entails.pure_right hp (Entails.pure_right hp (Entails.refl _))

theorem optAddrBuf_extract_cap (A : RustAlloc) (cap ptr len : BitVec 64) (addrOpt : Option (List (BitVec 8))) :
    optAddrBuf A cap ptr len addrOpt ⊢
      ⌜cap = if addrOpt.isSome then 36#64 else noneCap⌝ ∗ optAddrBuf A cap ptr len addrOpt := by
  cases addrOpt with
  | none =>
    simp only [optAddrBuf, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    exact Entails.pure_left fun hc => Entails.pure_right hc (Entails.pure_right hc (Entails.refl _))
  | some ad =>
    simp only [optAddrBuf, Option.isSome_some, ↓reduceIte]
    exact Entails.pure_left fun ⟨hc, hl, had⟩ => Entails.pure_right hc (Entails.pure_right ⟨hc, hl, had⟩ (Entails.refl _))

theorem cells3_3_3_eq_cells9 (sp0 : BitVec 64) :
    cells (sp0 - 288#64) 3 ∗ cells (sp0 - 264#64) 3 ∗ cells (sp0 - 240#64) 3 = cells (sp0 - 288#64) 9 := by
  rw [← memRegion_cells' (sp0 - 288#64) 24 3, ← memRegion_cells' (sp0 - 264#64) 24 3,
      ← memRegion_cells' (sp0 - 240#64) 24 3, ← memRegion_cells' (sp0 - 288#64) 72 9,
      memRegion_split' (b := sp0 - 288#64) (b' := sp0 - 264#64) (n := 24) (k := 48)
        rfl (bv_sub_add_lit sp0 288 24).symm (by decide),
      memRegion_split' (b := sp0 - 264#64) (b' := sp0 - 240#64) (n := 24) (k := 24)
        rfl (bv_sub_add_lit sp0 264 24).symm (by decide)]

theorem sepConj_assoc4_3_1 (P1 P2 P3 P4 : SepProp) : P1 ∗ P2 ∗ P3 ∗ P4 = (P1 ∗ P2 ∗ P3) ∗ P4 := by
  simp only [sepConj_assoc]

theorem optVecU8At_rk_unpack (A : RustAlloc) (sp0 rkPtr : BitVec 64) (pk : PublicKey) :
    optVecU8At A ⟨33#64, rkPtr⟩ (sp0 - 288#64) (some pk.serialize) ⊢
      cells (sp0 - 288#64) 3 ∗ boxU8Buf A rkPtr pk.serialize := by
  have hlen : pk.serialize.length = 33 := publicKey_serialize_length pk
  have heq := optVecU8At_some_exact_eq A (sp0 - 288#64) rkPtr pk.serialize (by omega)
  rw [hlen] at heq; rw [heq, sepConj_assoc4_3_1]
  exact sepConj_mono_left (three_words_entails_cells3 (sp0 - 288#64) 33#64 rkPtr 33#64)

theorem optVecU8At_ct_unpack (A : RustAlloc) (sp0 ctCopyPtr : BitVec 64) (ct : List (BitVec 8))
    (hct : ct.length ≤ 2 ^ 32) :
    optVecU8At A ⟨BitVec.ofNat 64 ct.length, ctCopyPtr⟩ (sp0 - 264#64) (some ct) ⊢
      cells (sp0 - 264#64) 3 ∗ boxU8Buf A ctCopyPtr ct := by
  rw [optVecU8At_some_exact_eq A (sp0 - 264#64) ctCopyPtr ct (by omega), sepConj_assoc4_3_1]
  exact sepConj_mono_left (three_words_entails_cells3 (sp0 - 264#64) _ ctCopyPtr _)

theorem optVecU8At_pq_unpack (A : RustAlloc) (sp0 pqCap pqCopyPtr : BitVec 64)
    (pq : List (BitVec 8)) (hpq_pin : PqPinOk pqCap pqCopyPtr pq) :
    optVecU8At A ⟨pqCap, pqCopyPtr⟩ (sp0 - 240#64) (if pq.isEmpty then none else some pq) ⊢
      cells (sp0 - 240#64) 3 ∗ optPqBuf A pqCap pqCopyPtr pq := by
  unfold PqPinOk optPqBuf at *; by_cases hemp : pq.isEmpty
  · simp only [hemp, ↓reduceIte] at hpq_pin ⊢; subst hpq_pin
    have htrue : (noneCap = noneCap) = True := eq_true rfl
    rw [optVecU8At_none_eq, htrue, pure_true, emp_sepConj, sepConj_emp,
        ← memRegion_cells' (sp0 - 240#64) 24 3,
        memRegion_split' (b := sp0 - 240#64) (b' := sp0 - 240#64 + 8#64) (n := 8) (k := 16)
          rfl rfl (by decide),
        memRegion_eight (sp0 - 240#64), memRegion_16_eq_cells2 (sp0 - 240#64 + 8#64)]
    have h16 : sp0 - 240#64 + 8#64 + 8#64 = sp0 - 240#64 + 16#64 := by bv_kernel
    rw [h16]; exact sepConj_mono_left (Entails.sepExists_intro noneCap)
  · simp only [hemp, Bool.false_eq_true, ↓reduceIte] at hpq_pin ⊢
    rcases hpq_pin with ⟨rfl, hpos, hlt, hne⟩
    have hne_nil : pq ≠ [] := List.isEmpty_eq_false_iff.mp (Bool.eq_false_iff.mpr hemp)
    rw [optVecU8At_some_exact_eq A (sp0 - 240#64) pqCopyPtr pq hlt, sepConj_assoc4_3_1]
    refine sepConj_mono (three_words_entails_cells3 (sp0 - 240#64) _ pqCopyPtr _) ?_
    simp only [boxU8Buf, hne_nil, ↓reduceIte]
    exact Entails.pure_left fun _ => Entails.pure_right ⟨trivial, hpos, hlt, hne⟩ (Entails.refl _)

theorem optVecU8At_addr_unpack (A : RustAlloc) (sp0 addrCap addrPtr : BitVec 64)
    (addrOpt : Option (List (BitVec 8))) (haddrCap : addrCap = if addrOpt.isSome then 36#64 else noneCap) :
    optVecU8At A ⟨addrCap, addrPtr⟩ (sp0 - 216#64) addrOpt ⊢ optSerializeAddressesAt A (sp0 - 216#64) addrOpt := by
  cases addrOpt with
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at haddrCap; subst haddrCap; exact Entails.refl _
  | some ad =>
    simp only [Option.isSome_some, ↓reduceIte] at haddrCap; subst haddrCap
    simp only [optVecU8At, optSerializeAddressesAt]
    exact @Entails.sepExists_intro _ (fun ptr => vecU8At A (sp0 - 216#64) 36#64 ptr ad) addrPtr

theorem optU32At_unpack (a : BitVec 64) (v : BitVec 32) :
    optU32At a (some v) ⊢ (∃∗ w0 : BitVec 32, a ↦₃₂ w0) ∗ (∃∗ w1 : BitVec 32, (a + 4#64) ↦₃₂ w1) :=
  sepConj_mono (Entails.sepExists_intro 1#32) (Entails.sepExists_intro v)

theorem wireSignalMessageAt_unpack_for_phase3 (A : RustAlloc) (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr : BitVec 64)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32) (hpq_pin : PqPinOk pqCap pqCopyPtr x.pqRatchet)
    (haddrCap : addrCap = if (x.addresses uuidTryParse).isSome then 36#64 else noneCap) :
    wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
      (sp0 - 288#64) (x.protoMsg uuidTryParse) ⊢
      cells (sp0 - 288#64) 9 ∗ optSerializeAddressesAt A (sp0 - 216#64) (x.addresses uuidTryParse) ∗
      (∃∗ w192 : BitVec 32, (sp0 - 192#64) ↦₃₂ w192) ∗ (∃∗ w188 : BitVec 32, (sp0 - 188#64) ↦₃₂ w188) ∗
      (∃∗ w184 : BitVec 32, (sp0 - 184#64) ↦₃₂ w184) ∗ (∃∗ w180 : BitVec 32, (sp0 - 180#64) ↦₃₂ w180) ∗
      boxU8Buf A rkPtr x.senderRatchetKey.serialize ∗ boxU8Buf A ctCopyPtr x.ciphertext ∗
      optPqBuf A pqCap pqCopyPtr x.pqRatchet := by
  have hrk := optVecU8At_rk_unpack A sp0 rkPtr x.senderRatchetKey
  have hct := optVecU8At_ct_unpack A sp0 ctCopyPtr x.ciphertext hct_bound
  have hpq := optVecU8At_pq_unpack A sp0 pqCap pqCopyPtr x.pqRatchet hpq_pin
  have haddr := optVecU8At_addr_unpack A sp0 addrCap addrPtr (x.addresses uuidTryParse) haddrCap
  have hu1 := optU32At_unpack (sp0 - 192#64) x.counter
  have hu2 := optU32At_unpack (sp0 - 184#64) x.previousCounter
  simp (disch := decide) only [bv_sub_add_lit, Nat.reduceSub] at hu1 hu2
  simp (disch := decide) only [wireSignalMessageAt, SignalMessageNewGhost.mkPins,
    SignalMessageNewGhost.protoMsg, bv_sub_add_lit, Nat.reduceSub]
  refine Entails.trans
    (sepConj_mono hrk (sepConj_mono hct (sepConj_mono hpq (sepConj_mono haddr (sepConj_mono hu1 hu2))))) ?_
  rw [← cells3_3_3_eq_cells9 sp0]; exact Entails.of_eq (by ac_rfl)

theorem signalMessageNew_subroutine_ok_of_sepWPp {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} {Ppost : α → State → SepProp}
    (hpost : ∀ x s0 sf, sf.trace = s0.trace → (Ppost x s0 ⊢ spec.post x s0 sf))
    (hpan : ∀ x s0 sf, spec.onPanic x s0 sf = (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap))
    (h : ∀ (x : α) (s0 : State), s0.pc = entry → s0.status = .Running → s0.spAligned = true →
      SepWPp prog (s0.readReg64 Reg.lr) s0 (spec.pre x s0)
        (fun sf P_f => (sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) ∧ (P_f ⊢ Ppost x s0))
        (PanicAllocPost s0)) :
    subroutine_ok prog entry spec := by
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp; refine ⟨spec.pre x s0, R, hpre, ?_⟩
  intro R' hm hL
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, ⟨hspf, hcsf, htrf⟩, hent⟩ | ⟨hpanf, P_f, hmf, hqp⟩ | ⟨_, hoom⟩⟩ :=
    h x s0 hpc hrun hsp R' hm hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, P_f, hmf, fun hmFr => ?_, hspf, hcsf⟩⟩
    exact Satisfies.mono (sepConj_mono_left (Entails.trans hent (hpost x s0 sf htrf))) hmFr
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpanf, P_f, hmf, fun hmFr => ?_⟩)⟩
    rw [hpan x s0 sf]; exact hqp R hmFr
  · exact (not_satisfies_false_sepConj hoom).elim

theorem memRegion_wire_112_rest (sp0 : BitVec 64) (R : SepProp) :
    cells (sp0 - 288#64) 12 ∗ (∃∗ w192 : BitVec 32, (sp0 - 192#64) ↦₃₂ w192) ∗
    (∃∗ w188 : BitVec 32, (sp0 - 188#64) ↦₃₂ w188) ∗ (∃∗ w184 : BitVec 32, (sp0 - 184#64) ↦₃₂ w184) ∗
    (∃∗ w180 : BitVec 32, (sp0 - 180#64) ↦₃₂ w180) ∗ R = memRegion (sp0 - 288#64) 112 ∗ R := by
  rw [memRegion_wire_112 sp0]; simp only [sepConj_assoc]

theorem stackAt_signalMessageNewStack_ready (sp0 : BitVec 64) :
    stackAt sp0 signalMessageNewStack =
      (∃∗ w408 : BitVec 64, ∃∗ w400 : BitVec 64, ∃∗ w392 : BitVec 64,
       ∃∗ w384 : BitVec 32, ∃∗ w380 : BitVec 32,
       ∃∗ w376 : BitVec 64, ∃∗ w368 : BitVec 64, ∃∗ w360 : BitVec 64,
       ∃∗ w352 : BitVec 64, ∃∗ w344 : BitVec 64, ∃∗ w332 : BitVec 32,
       ∃∗ w328 : BitVec 64, ∃∗ w320 : BitVec 64,
       ∃∗ w176 : BitVec 64, ∃∗ w168 : BitVec 64, ∃∗ w160 : BitVec 64,
        stackAt (sp0 - 416#64) computeMacStack ∗ newUnusedPad sp0 ∗
        ((sp0 - 408#64) ↦₆₄ w408) ∗ ((sp0 - 400#64) ↦₆₄ w400) ∗ ((sp0 - 392#64) ↦₆₄ w392) ∗
        ((sp0 - 384#64) ↦₃₂ w384) ∗ ((sp0 - 380#64) ↦₃₂ w380) ∗ ((sp0 - 376#64) ↦₆₄ w376) ∗
        ((sp0 - 368#64) ↦₆₄ w368) ∗ ((sp0 - 360#64) ↦₆₄ w360) ∗ ((sp0 - 352#64) ↦₆₄ w352) ∗
        ((sp0 - 344#64) ↦₆₄ w344) ∗ ((sp0 - 332#64) ↦₃₂ w332) ∗ ((sp0 - 328#64) ↦₆₄ w328) ∗
        ((sp0 - 320#64) ↦₆₄ w320) ∗ memRegion (sp0 - 312#64) 24 ∗ memRegion (sp0 - 288#64) 112 ∗
        ((sp0 - 176#64) ↦₆₄ w176) ∗ ((sp0 - 168#64) ↦₆₄ w168) ∗ ((sp0 - 160#64) ↦₆₄ w160) ∗
        memRegion (sp0 - 152#64) 16 ∗ cells (sp0 - 96#64) 12) := by
  have h408 : cells (sp0 - 408#64) 3 =
      (∃∗ w408 : BitVec 64, (sp0 - 408#64) ↦₆₄ w408 ∗
       ∃∗ w400 : BitVec 64, (sp0 - 400#64) ↦₆₄ w400 ∗ ∃∗ w392 : BitVec 64, (sp0 - 392#64) ↦₆₄ w392) := by
    simp (disch := decide) only [cells, sepConj_emp, bv_sub_add_lit, Nat.reduceSub]
  have h376 : cells (sp0 - 376#64) 5 =
      (∃∗ w376 : BitVec 64, (sp0 - 376#64) ↦₆₄ w376 ∗ ∃∗ w368 : BitVec 64, (sp0 - 368#64) ↦₆₄ w368 ∗
       ∃∗ w360 : BitVec 64, (sp0 - 360#64) ↦₆₄ w360 ∗ ∃∗ w352 : BitVec 64, (sp0 - 352#64) ↦₆₄ w352 ∗
       ∃∗ w344 : BitVec 64, (sp0 - 344#64) ↦₆₄ w344) := by
    simp (disch := decide) only [cells, sepConj_emp, bv_sub_add_lit, Nat.reduceSub]
  have h328 : cells (sp0 - 328#64) 2 =
      (∃∗ w328 : BitVec 64, (sp0 - 328#64) ↦₆₄ w328 ∗ ∃∗ w320 : BitVec 64, (sp0 - 320#64) ↦₆₄ w320) := by
    simp (disch := decide) only [cells, sepConj_emp, bv_sub_add_lit, Nat.reduceSub]
  have h176 : cells (sp0 - 176#64) 3 =
      (∃∗ w176 : BitVec 64, (sp0 - 176#64) ↦₆₄ w176 ∗
       ∃∗ w168 : BitVec 64, (sp0 - 168#64) ↦₆₄ w168 ∗ ∃∗ w160 : BitVec 64, (sp0 - 160#64) ↦₆₄ w160) := by
    simp (disch := decide) only [cells, sepConj_emp, bv_sub_add_lit, Nat.reduceSub]
  rw [stackAt_signalMessageNewStack_split sp0, memRegion_wire_112_rest sp0]
  simp only [h408, h376, h328, h176, sepExists_sepConj_left, sepConj_assoc]; simp only [sepExists_sepConj_right]

theorem stackAt_signalMessageNewStackX_ready (sp0 : BitVec 64) :
    stackAt sp0 signalMessageNewStackX =
      (∃∗ w408 : BitVec 64, ∃∗ w400 : BitVec 64, ∃∗ w392 : BitVec 64,
       ∃∗ w384 : BitVec 32, ∃∗ w380 : BitVec 32,
       ∃∗ w376 : BitVec 64, ∃∗ w368 : BitVec 64, ∃∗ w360 : BitVec 64,
       ∃∗ w352 : BitVec 64, ∃∗ w344 : BitVec 64, ∃∗ w332 : BitVec 32,
       ∃∗ w328 : BitVec 64, ∃∗ w320 : BitVec 64,
       ∃∗ w176 : BitVec 64, ∃∗ w168 : BitVec 64, ∃∗ w160 : BitVec 64,
        stackAt (sp0 - 416#64) computeMacStackX ∗ newUnusedPad sp0 ∗
        ((sp0 - 408#64) ↦₆₄ w408) ∗ ((sp0 - 400#64) ↦₆₄ w400) ∗ ((sp0 - 392#64) ↦₆₄ w392) ∗
        ((sp0 - 384#64) ↦₃₂ w384) ∗ ((sp0 - 380#64) ↦₃₂ w380) ∗ ((sp0 - 376#64) ↦₆₄ w376) ∗
        ((sp0 - 368#64) ↦₆₄ w368) ∗ ((sp0 - 360#64) ↦₆₄ w360) ∗ ((sp0 - 352#64) ↦₆₄ w352) ∗
        ((sp0 - 344#64) ↦₆₄ w344) ∗ ((sp0 - 332#64) ↦₃₂ w332) ∗ ((sp0 - 328#64) ↦₆₄ w328) ∗
        ((sp0 - 320#64) ↦₆₄ w320) ∗ memRegion (sp0 - 312#64) 24 ∗ memRegion (sp0 - 288#64) 112 ∗
        ((sp0 - 176#64) ↦₆₄ w176) ∗ ((sp0 - 168#64) ↦₆₄ w168) ∗ ((sp0 - 160#64) ↦₆₄ w160) ∗
        memRegion (sp0 - 152#64) 16 ∗ cells (sp0 - 96#64) 12) := by
  have h408 : cells (sp0 - 408#64) 3 =
      (∃∗ w408 : BitVec 64, (sp0 - 408#64) ↦₆₄ w408 ∗
       ∃∗ w400 : BitVec 64, (sp0 - 400#64) ↦₆₄ w400 ∗ ∃∗ w392 : BitVec 64, (sp0 - 392#64) ↦₆₄ w392) := by
    simp (disch := decide) only [cells, sepConj_emp, bv_sub_add_lit, Nat.reduceSub]
  have h376 : cells (sp0 - 376#64) 5 =
      (∃∗ w376 : BitVec 64, (sp0 - 376#64) ↦₆₄ w376 ∗ ∃∗ w368 : BitVec 64, (sp0 - 368#64) ↦₆₄ w368 ∗
       ∃∗ w360 : BitVec 64, (sp0 - 360#64) ↦₆₄ w360 ∗ ∃∗ w352 : BitVec 64, (sp0 - 352#64) ↦₆₄ w352 ∗
       ∃∗ w344 : BitVec 64, (sp0 - 344#64) ↦₆₄ w344) := by
    simp (disch := decide) only [cells, sepConj_emp, bv_sub_add_lit, Nat.reduceSub]
  have h328 : cells (sp0 - 328#64) 2 =
      (∃∗ w328 : BitVec 64, (sp0 - 328#64) ↦₆₄ w328 ∗ ∃∗ w320 : BitVec 64, (sp0 - 320#64) ↦₆₄ w320) := by
    simp (disch := decide) only [cells, sepConj_emp, bv_sub_add_lit, Nat.reduceSub]
  have h176 : cells (sp0 - 176#64) 3 =
      (∃∗ w176 : BitVec 64, (sp0 - 176#64) ↦₆₄ w176 ∗
       ∃∗ w168 : BitVec 64, (sp0 - 168#64) ↦₆₄ w168 ∗ ∃∗ w160 : BitVec 64, (sp0 - 160#64) ↦₆₄ w160) := by
    simp (disch := decide) only [cells, sepConj_emp, bv_sub_add_lit, Nat.reduceSub]
  rw [stackAt_signalMessageNewStackX_split sp0, memRegion_wire_112_rest sp0]
  simp only [h408, h376, h328, h176, sepExists_sepConj_left, sepConj_assoc]
  simp only [sepExists_sepConj_right]

/-! ## Main theorem: `signalMessageNew_ok'` -/

set_option maxHeartbeats 3200000 in
theorem signalMessageNew_ok_ext {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts img.base A ext)
    (hPk : PublicKeySerializeOkExt img.base A ext) (hEncLen : EncodedLenOkExt img.base A ext)
    (hVarint : EncodeVarintOkExt img.base A ext) (hSerAddr : SerializeAddressesOkExt img.base A uuidTryParse ext)
    (hMac : ComputeMacOkExt img C A ext) : SignalMessageNewOkExt img C A uuidTryParse ext := by
  apply signalMessageNew_subroutine_ok_of_sepWPp
    (Ppost := fun x s0 => x.inputsAt A s0.sp ∗
      (∃∗ g : SignalMessageGhost, signalMessageAt A g x.ret (x.model C.F uuidTryParse)) ∗
      A.pool ∗ stackAt s0.sp signalMessageNewStack)
    (fun x s0 sf htr => by simp only [Spec.inImage, signalMessageNewSpec]; exact Entails.pure_right htr (Entails.refl _))
    (fun _ _ _ => rfl)
  intro x s0 hpc hrun hsp_align
  simp only [Spec.inImage, signalMessageNewSpec, SignalMessageNewGhost.inputsAt, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hF0, hsym0⟩ => ?_
  refine SepWPp.pure_elim fun ⟨hx0, hx1, hx2, hx3, hloc_ne, hx4, hx5, hx6, hx7, hx8, hct_bound, hpq_bound⟩ => ?_
  conv => arg 4; rw [stackAt_signalMessageNewStack_ready s0.sp]; simp only [sepExists_sepConj_right]
  refine SepWPp.exists_elim fun w408 => SepWPp.exists_elim fun w400 =>
    SepWPp.exists_elim fun w392 => SepWPp.exists_elim fun w384 =>
    SepWPp.exists_elim fun w380 => SepWPp.exists_elim fun w376 =>
    SepWPp.exists_elim fun w368 => SepWPp.exists_elim fun w360 =>
    SepWPp.exists_elim fun w352 => SepWPp.exists_elim fun w344 =>
    SepWPp.exists_elim fun w332 => SepWPp.exists_elim fun w328 =>
    SepWPp.exists_elim fun w320 => SepWPp.exists_elim fun w176 =>
    SepWPp.exists_elim fun w168 => SepWPp.exists_elim fun w160 => ?_
  refine signalMessageNew_seg3_seq_wp_inImage' hF0 hsym0
    (new_prologue_wp_ext x s0.sp w368 w360 w352 w344 w328 w332 s0 hpc hrun rfl hsp_align hx1 hx2 hx4 hx5 hx6 hx7 hx8)
    (by sep_focus) ?_
  intro s1 hpc1 hrun1 hF1 hsym1 ⟨hsp1, hsp_align1, hx3_1, hx4_1, hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hx27_1, hx29_1, htr1⟩
  refine signalMessageNew_seg3_seq_wpp_inImage' htr1 hF1 hsym1
    (new_addr_and_rk_wpp_ext hPk hSerAddr x s0.sp s1 hpc1 hrun1 hsp1 hsp_align1 (hx3_1.trans hx3) hloc_ne hx4_1
      hx19_1 hx20_1 hx22_1 hx23_1 hx24_1 hx25_1 hx27_1 hx29_1)
    (by sep_focus) (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s2 hpc2 hrun2 hF2 hsym2 ⟨hsp2, hsp_align2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx27_2, hx29_2, htr2⟩
  have htr2' : TraceVRegsEq s2 s0 := htr2.trans htr1
  refine signalMessageNew_seg3_seq_wpp_inImage' htr2' hF2 hsym2
    (new_ct_copy_wpp_ext hA x s0.sp (s2.readReg64 .x28) w400 hct_bound s2
      hpc2 hrun2 hsp2 hsp_align2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx27_2 rfl hx29_2)
    (by sep_focus) (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s3 hpc3 hrun3 hF3 hsym3 ⟨hsp3, hsp_align3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx27_3, hx28_3, hx29_3, htr3⟩
  have htr3' : TraceVRegsEq s3 s0 := htr3.trans htr2'
  refine signalMessageNew_seg3_seq_wpp_inImage' htr3' hF3 hsym3
    (new_pq_copy_wpp_ext hA x s0.sp (s2.readReg64 .x28) (s3.readReg64 .x26) hpq_bound s3
      hpc3 hrun3 hsp3 hsp_align3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 rfl hx27_3 hx28_3 hx29_3)
    (by sep_focus) (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s4 hpc4 hrun4 hF4 hsym4 ⟨hsp4, hsp_align4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx26_4, hx27_4, hx28_4, hx29_4, htr4⟩
  have htr4' : TraceVRegsEq s4 s0 := htr4.trans htr3'
  refine SepWPp.fold (optSerializeAddressesAt_unpack A (s0.sp - 312#64) x) (by sep_focus) ?_
  conv => arg 4; simp (disch := decide) only [bv_sub_add_lit, Nat.reduceSub, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun addrCap => SepWPp.exists_elim fun addrPtr => SepWPp.exists_elim fun addrLen => ?_
  refine SepWPp.fold (optPqBuf_extract_pin A (s4.readReg64 .x9) (s4.readReg64 .x25) x.pqRatchet) (by sep_focus) ?_
  simp only [sepConj_assoc]; refine SepWPp.pure_elim fun hpq_pin => ?_
  refine SepWPp.fold (optAddrBuf_extract_cap A addrCap addrPtr addrLen (x.addresses uuidTryParse)) (by sep_focus) ?_
  simp only [sepConj_assoc]; refine SepWPp.pure_elim fun haddrCap => ?_
  have hrk_buf : boxU8Buf A (s2.readReg64 .x28) x.senderRatchetKey.serialize =
      signalMessageNew_vecU8Buf A 33#64 (s2.readReg64 .x28) x.senderRatchetKey.serialize := by
    have hlen : x.senderRatchetKey.serialize.length = 33 := publicKey_serialize_length x.senderRatchetKey
    have h := (vecU8Buf_eq_boxU8Buf A (s2.readReg64 .x28) x.senderRatchetKey.serialize (by omega)).symm
    rw [hlen] at h; exact h
  rw [hrk_buf]
  refine signalMessageNew_seg3_seq_wp_inImage' hF4 hsym4
    (new_store_wire_wp_ext x s0.sp (s2.readReg64 .x28) (s3.readReg64 .x26) (s4.readReg64 .x9) (s4.readReg64 .x25)
      addrCap addrPtr addrLen w376 w320 hct_bound s4 hpc4 hrun4 hsp4 hsp_align4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4
      hx24_4 rfl hx26_4 hx27_4 hx28_4 hx29_4 rfl)
    (by sep_focus) ?_
  intro s5 hpc5 hrun5 hF5 hsym5 ⟨hsp5, hsp_align5, hx0_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hx29_5, htr5⟩
  have htr5' : TraceVRegsEq s5 s0 := htr5.trans htr4'
  have hver32 : ((s0.readReg64 .x0).setWidth 32).setWidth 8 = x.messageVersion := by rw [← hx0]; bv_kernel
  refine signalMessageNew_seg3_seq_wpp_inImage' htr5' hF5 hsym5
    (new_alloc_ser_wpp_ext hA hEncLen x s0.sp (s2.readReg64 .x28) (s3.readReg64 .x26) (s4.readReg64 .x9) (s4.readReg64 .x25)
      addrCap addrPtr w176 w168 w160 w384 w380 ((s0.readReg64 .x0).setWidth 32) hver32 hct_bound hpq_bound s5
      hpc5 hrun5 hsp5 hsp_align5 hx0_5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx24_5 hx25_5 hx26_5 hx27_5 hx28_5 hx29_5)
    (by sep_focus) (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s6 hpc6 hrun6 hF6 hsym6 ⟨hsp6, hsp_align6, hx19_6, hx20_6, hx21_6, hx22_6, _hx23_6, hx24_6, hx25_6, hx26_6, hx27_6, hx28_6, hx29_6, htr6⟩
  have htr6' : TraceVRegsEq s6 s0 := htr6.trans htr5'
  refine signalMessageNew_seg3_seq_wpp_inImage' htr6' hF6 hsym6
    (new_encode_tag1_wpp_ext hA hVarint x s0.sp (s2.readReg64 .x28) (s3.readReg64 .x26) (s4.readReg64 .x9) (s4.readReg64 .x25)
      addrCap addrPtr (s6.readReg64 .x22) hct_bound hpq_bound hx22_6 s6 hpc6 hrun6 hsp6 hsp_align6 hx19_6 hx20_6
      hx21_6 rfl hx24_6 hx25_6 hx26_6 hx27_6 hx28_6 hx29_6)
    (by sep_focus) (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s7 hpc7 hrun7 hF7 hsym7 ⟨hsp7, hsp_align7, hx19_7, hx20_7, hx21_7, hx22_7, hx23_7, hx24_7, hx25_7, hx26_7, hx27_7, hx28_7, hx29_7, htr7⟩
  have htr7' : TraceVRegsEq s7 s0 := htr7.trans htr6'
  refine signalMessageNew_seg3_seq_wpp_inImage' htr7' hF7 hsym7
    (new_encode_tag2_wpp_ext hVarint x s0.sp (s2.readReg64 .x28) (s3.readReg64 .x26) (s4.readReg64 .x25) (s6.readReg64 .x22)
      hct_bound hpq_bound hx22_6 s7 hpc7 hrun7 hsp7 hsp_align7 hx19_7 hx20_7 hx21_7 hx22_7 hx23_7 hx24_7 hx25_7 hx26_7 hx27_7 hx28_7 hx29_7)
    (by sep_focus) (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s8 hpc8 hrun8 hF8 hsym8 ⟨hsp8, hsp_align8, hx19_8, hx21_8, hx23_8, hx24_8, hx25_8, hx26_8, hx27_8, hx28_8, hx29_8, htr8⟩
  have htr8' : TraceVRegsEq s8 s0 := htr8.trans htr7'
  refine signalMessageNew_seg3_seq_wpp_inImage' htr8' hF8 hsym8
    (new_encode_tag3_wpp_ext hVarint x s0.sp (s2.readReg64 .x28) (s3.readReg64 .x26) (s4.readReg64 .x9) (s4.readReg64 .x25) (s6.readReg64 .x22)
      hct_bound hpq_bound hx22_6 s8 hpc8 hrun8 hsp8 hsp_align8 hx19_8 hx21_8 hx23_8 hx24_8 hx25_8 hx26_8 hx27_8 hx28_8 hx29_8)
    (by sep_focus) (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s9 hpc9 hrun9 hF9 hsym9 ⟨hsp9, hsp_align9, hx19_9, hx20_9, hx21_9, hx23_9, hx24_9, hx25_9, hx26_9, hx27_9, hx28_9, hx29_9, htr9⟩
  have htr9' : TraceVRegsEq s9 s0 := htr9.trans htr8'
  refine signalMessageNew_seg3_seq_wpp_inImage' htr9' hF9 hsym9
    (new_encode_tag4_wpp_ext hA hVarint x s0.sp (s2.readReg64 .x28) (s3.readReg64 .x26) (s4.readReg64 .x9) (s4.readReg64 .x25)
      addrCap addrPtr (s6.readReg64 .x22) w392 hct_bound hpq_bound hx22_6 s9 hpc9 hrun9 hsp9 hsp_align9 hx19_9 hx20_9
      hx21_9 hx23_9 hx24_9 hx25_9 hx26_9 hx27_9 hx28_9 hx29_9)
    (by sep_focus) (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s10 hpc10 hrun10 hF10 hsym10 ⟨hsp10, hsp_align10, hx19_10, hx20_10, hx21_10, hx23_10, hx24_10, hx25_10, hx26_10, hx27_10, hx28_10, hx29_10, htr10⟩
  have htr10' : TraceVRegsEq s10 s0 := htr10.trans htr9'
  refine signalMessageNew_seg3_seq_wpp_inImage' htr10' hF10 hsym10
    (new_encode_tag56_wpp_ext hA hVarint x s0.sp (s2.readReg64 .x28) (s3.readReg64 .x26) (s4.readReg64 .x9) (s4.readReg64 .x25)
      addrCap addrPtr (s6.readReg64 .x22) w408 hct_bound hpq_bound hx22_6 hpq_pin haddrCap s10 hpc10 hrun10 hsp10 hsp_align10
      hx19_10 hx20_10 hx21_10 hx23_10 hx24_10 hx25_10 hx26_10 hx27_10 hx28_10 hx29_10)
    (by sep_focus) (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s11 hpc11 hrun11 hF11 hsym11 ⟨hsp11, hsp_align11, hx19_11, hx20_11, hx21_11, hx22_11, _hx23_11, hx24_11, hx25_11, hx27_11, hx29_11, htr11⟩
  have htr11' : TraceVRegsEq s11 s0 := htr11.trans htr10'
  refine SepWPp.fold
    (wireSignalMessageAt_unpack_for_phase3 A x s0.sp (s2.readReg64 .x28)
      (s3.readReg64 .x26) (s4.readReg64 .x9) (s4.readReg64 .x25) addrCap addrPtr hct_bound hpq_pin haddrCap)
    (by sep_focus) ?_
  rw [show (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9 =
      1 + (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 8 by omega]
  simp only [sepConj_assoc]
  have hstep8 := new_phase3_wpp_ext hA hMac x s0.sp (s6.readReg64 .x22) (s2.readReg64 .x28)
    (s3.readReg64 .x26) (s4.readReg64 .x9) (s4.readReg64 .x25) addrCap
    ((s0.readReg64 .x0).setWidth 32) hver32 haddrCap hct_bound hpq_bound
    s0 s11 hF11 hsym11 hpc11 hrun11 hsp11 rfl hsp_align hsp_align11
    hx19_11 hx20_11 hx21_11 hx22_11 hx24_11 hx25_11 hx27_11 hx29_11 htr11'
  have hfocus :
      (cells (s0.sp - 288#64) 9 ∗ optSerializeAddressesAt A (s0.sp - 216#64) (x.addresses uuidTryParse) ∗
        (∃∗ w192 : BitVec 32, (s0.sp - 192#64) ↦₃₂ w192) ∗ (∃∗ w188 : BitVec 32, (s0.sp - 188#64) ↦₃₂ w188) ∗
        (∃∗ w184 : BitVec 32, (s0.sp - 184#64) ↦₃₂ w184) ∗ (∃∗ w180 : BitVec 32, (s0.sp - 180#64) ↦₃₂ w180) ∗
        boxU8Buf A (s2.readReg64 .x28) x.senderRatchetKey.serialize ∗ boxU8Buf A (s3.readReg64 .x26) x.ciphertext ∗
        optPqBuf A (s4.readReg64 .x9) (s4.readReg64 .x25) x.pqRatchet ∗
        ((s0.sp - 408#64) ↦₆₄ s2.readReg64 .x28) ∗ ((s0.sp - 392#64) ↦₆₄ s4.readReg64 .x25) ∗
        ((s0.sp - 344#64) ↦₆₄ s3.readReg64 .x26) ∗
        vecU8At A (s0.sp - 176#64)
          (BitVec.ofNat 64 (1 + (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 8))
          (s6.readReg64 .x22) (x.serPrefix6 uuidTryParse) ∗
        A.pool ∗ stackAt (s0.sp - 416#64) computeMacStack ∗ ((s0.sp - 320#64) ↦₆₄ s4.readReg64 .x9) ∗
        ((s0.sp - 384#64) ↦₃₂ x.counter) ∗ ((s0.sp - 380#64) ↦₃₂ x.previousCounter) ∗
        ((s0.sp - 332#64) ↦₃₂ (s0.readReg64 .x0).setWidth 32) ∗ ((s0.sp - 376#64) ↦₆₄ x.senderRatchetKeyA) ∗
        memRegion (s0.sp - 312#64) 24 ∗ ((s0.sp - 328#64) ↦₆₄ x.pqRatchetA) ∗
        (x.pqRatchetA ↦ₛ x.pqRatchet) ∗ ((s0.sp - 400#64) ↦₆₄ x.ciphertextA) ∗
        (x.ciphertextA ↦ₛ x.ciphertext) ∗ optAddrAt A x.locA x.loc ∗ protocolAddressAt A x.rem x.remA ∗
        (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗ (s0.sp ↦₆₄ x.ciphertextA) ∗
        ((s0.sp + 8#64) ↦₆₄ BitVec.ofNat 64 x.ciphertext.length) ∗ ((s0.sp + 16#64) ↦₆₄ x.senderIkA) ∗
        ((s0.sp + 24#64) ↦₆₄ x.receiverIkA) ∗ ((s0.sp + 32#64) ↦₆₄ x.pqRatchetA) ∗
        ((s0.sp + 40#64) ↦₆₄ BitVec.ofNat 64 x.pqRatchet.length) ∗
        ((s0.sp - 368#64) ↦₆₄ x.senderIkA) ∗ ((s0.sp - 360#64) ↦₆₄ x.receiverIkA) ∗
        ((s0.sp - 352#64) ↦₆₄ x.macKeyA) ∗ newSavedRegs s0.sp s0 ∗ (x.macKeyA ↦ₛ keyToBytes32 x.macKey) ∗
        (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗ (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
        memRegion x.ret 120 ∗ newUnusedPad s0.sp ∗ memRegion (s0.sp - 152#64) 16) =
      (newUnusedPad s0.sp ∗ ((s0.sp - 408#64) ↦₆₄ s2.readReg64 .x28) ∗ ((s0.sp - 400#64) ↦₆₄ x.ciphertextA) ∗
        ((s0.sp - 392#64) ↦₆₄ s4.readReg64 .x25) ∗ ((s0.sp - 384#64) ↦₃₂ x.counter) ∗
        ((s0.sp - 380#64) ↦₃₂ x.previousCounter) ∗ ((s0.sp - 376#64) ↦₆₄ x.senderRatchetKeyA) ∗
        ((s0.sp - 368#64) ↦₆₄ x.senderIkA) ∗ ((s0.sp - 360#64) ↦₆₄ x.receiverIkA) ∗
        ((s0.sp - 352#64) ↦₆₄ x.macKeyA) ∗ ((s0.sp - 344#64) ↦₆₄ s3.readReg64 .x26) ∗
        ((s0.sp - 332#64) ↦₃₂ (s0.readReg64 .x0).setWidth 32) ∗ ((s0.sp - 328#64) ↦₆₄ x.pqRatchetA) ∗
        ((s0.sp - 320#64) ↦₆₄ s4.readReg64 .x9) ∗ memRegion (s0.sp - 312#64) 24 ∗ cells (s0.sp - 288#64) 9 ∗
        optSerializeAddressesAt A (s0.sp - 216#64) (x.addresses uuidTryParse) ∗
        (∃∗ w192 : BitVec 32, (s0.sp - 192#64) ↦₃₂ w192) ∗ (∃∗ w188 : BitVec 32, (s0.sp - 188#64) ↦₃₂ w188) ∗
        (∃∗ w184 : BitVec 32, (s0.sp - 184#64) ↦₃₂ w184) ∗ (∃∗ w180 : BitVec 32, (s0.sp - 180#64) ↦₃₂ w180) ∗
        vecU8At A (s0.sp - 176#64)
          (BitVec.ofNat 64 (1 + (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 8))
          (s6.readReg64 .x22) (x.serPrefix6 uuidTryParse) ∗
        memRegion (s0.sp - 152#64) 16 ∗ newSavedRegs s0.sp s0 ∗
        (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
        (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
        (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
        (x.macKeyA ↦ₛ keyToBytes32 x.macKey) ∗ (x.ciphertextA ↦ₛ x.ciphertext) ∗
        (x.pqRatchetA ↦ₛ x.pqRatchet) ∗ boxU8Buf A (s2.readReg64 .x28) x.senderRatchetKey.serialize ∗
        boxU8Buf A (s3.readReg64 .x26) x.ciphertext ∗ optPqBuf A (s4.readReg64 .x9) (s4.readReg64 .x25) x.pqRatchet ∗
        memRegion x.ret 120 ∗ A.pool ∗ stackAt (s0.sp - 416#64) computeMacStack) ∗
      (optAddrAt A x.locA x.loc ∗ protocolAddressAt A x.rem x.remA ∗ (s0.sp ↦₆₄ x.ciphertextA) ∗
        ((s0.sp + 8#64) ↦₆₄ BitVec.ofNat 64 x.ciphertext.length) ∗ ((s0.sp + 16#64) ↦₆₄ x.senderIkA) ∗
        ((s0.sp + 24#64) ↦₆₄ x.receiverIkA) ∗ ((s0.sp + 32#64) ↦₆₄ x.pqRatchetA) ∗
        ((s0.sp + 40#64) ↦₆₄ BitVec.ofNat 64 x.pqRatchet.length)) := by ac_rfl
  intro R hm hL
  rw [hfocus, sepConj_assoc] at hm
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, hregs, hent⟩ | ⟨hpan_s, P_f, hmf, hp⟩ | ⟨_, hoom⟩⟩ :=
    hstep8 _ hm hL
  · have hmf' : sf.mem ⊨ (P_f ∗
        (optAddrAt A x.locA x.loc ∗ protocolAddressAt A x.rem x.remA ∗ (s0.sp ↦₆₄ x.ciphertextA) ∗
          ((s0.sp + 8#64) ↦₆₄ BitVec.ofNat 64 x.ciphertext.length) ∗ ((s0.sp + 16#64) ↦₆₄ x.senderIkA) ∗
          ((s0.sp + 24#64) ↦₆₄ x.receiverIkA) ∗ ((s0.sp + 32#64) ↦₆₄ x.pqRatchetA) ∗
          ((s0.sp + 40#64) ↦₆₄ BitVec.ofNat 64 x.pqRatchet.length))) ∗ R := by
      rw [sepConj_assoc]; exact hmf
    refine ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, _, hmf', hregs,
      Entails.trans (sepConj_mono_left hent) (Entails.of_eq (by ac_rfl))⟩⟩
  · have hmf' : sf.mem ⊨ (P_f ∗
        (optAddrAt A x.locA x.loc ∗ protocolAddressAt A x.rem x.remA ∗ (s0.sp ↦₆₄ x.ciphertextA) ∗
          ((s0.sp + 8#64) ↦₆₄ BitVec.ofNat 64 x.ciphertext.length) ∗ ((s0.sp + 16#64) ↦₆₄ x.senderIkA) ∗
          ((s0.sp + 24#64) ↦₆₄ x.receiverIkA) ∗ ((s0.sp + 32#64) ↦₆₄ x.pqRatchetA) ∗
          ((s0.sp + 40#64) ↦₆₄ BitVec.ofNat 64 x.pqRatchet.length))) ∗ R := by
      rw [sepConj_assoc]; exact hmf
    have halloc := hp _ hmf
    rw [sepConj_assoc, satisfies_pure_sepConj] at halloc
    exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan_s, _, hmf', panicAllocPost_of_eq halloc.1⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem signalMessageNew_ok' {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs)
    (hPk : PublicKeySerializeOk img.base C A ctl abs) (hEncLen : EncodedLenOk img.base C A ctl abs)
    (hVarint : EncodeVarintOk img.base C A ctl abs) (hSerAddr : SerializeAddressesOk img.base C A ctl uuidTryParse abs)
    (hMac : ComputeMacOk img C A ctl abs) : SignalMessageNewOk img C A ctl uuidTryParse abs :=
  signalMessageNew_ok_ext (AllocContracts.of_tripleRatchetProgAt img.base C A ctl abs hA)
    hPk hEncLen hVarint hSerAddr hMac

theorem signalMessageNew_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs)
    (hPk : PublicKeySerializeOk img.base C A ctl abs) (hEncLen : EncodedLenOk img.base C A ctl abs)
    (hVarint : EncodeVarintOk img.base C A ctl abs) (hSerAddr : SerializeAddressesOk img.base C A ctl uuidTryParse abs)
    (hMac : ComputeMacOk img C A ctl abs) : SignalMessageNewOk img C A ctl uuidTryParse abs :=
  signalMessageNew_ok' hA hPk hEncLen hVarint hSerAddr hMac

/-! ## Relocatable `[LibsignalPlacement]` theorem (Block `63`) -/

private def withMemInv {α : Type} (Inv : Memory → Prop) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s => spec.pre x s ∗ ⌜Inv s.mem⌝ }

private theorem signalMessageNew_of_sepWP_placed_gen {Inv : Memory → Prop}
    (hInv_kf : ∀ {m m'}, Inv m → Memory.KeepsFrozen m m' → Inv m')
    {prog : Program} (mid : BitVec 64) {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hinv : Inv s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      Inv sm.mem →
      SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hkont⟩ | ⟨_, hoom⟩⟩
  · obtain ⟨sf, hsteps', hout⟩ := hkont (hInv_kf hinv hsteps.keepsFrozen) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem signalMessageNew_call_placed_gen {Inv : Memory → Prop}
    (hInv_kf : ∀ {m m'}, Inv m → Memory.KeepsFrozen m m' → Inv m')
    {α : Type} {prog : Program} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    {entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {F : SepProp}
    (hinv : Inv s.mem)
    (hcall : subroutine_ok prog entry (withMemInv Inv spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, Inv sf.mem →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ ho; exact not_satisfies_false_sepConj ho) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hpre' : s.mem ⊨ (withMemInv Inv spec).pre x s ∗ (F ∗ R) := by
    dsimp only [withMemInv]
    rw [sepConj_comm (spec.pre x s), sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, hpre R hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun hpre' hsp hL
  have hinv_m : Inv sm.mem := hInv_kf hinv hsteps.keepsFrozen
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_s, hpost⟩
  · dsimp only [withMemInv] at hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hinv_m hpcm hrunm hspm hcsm R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withMemInv] at hpost
    rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost, hpanic sm hpan⟩)⟩
  · dsimp only [withMemInv] at hpost
    exact (hexit sm code _ hex hpost).elim
  · dsimp only [withMemInv] at hpost
    exact (hoom sm _ hoom_s hpost).elim

theorem signalMessageNew_seg3_seq_wpp_placed_gen' {Inv : Memory → Prop}
    (hInv_kf : ∀ {m m'}, Inv m → Memory.KeepsFrozen m m' → Inv m')
    {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {P P1 F : SepProp} {P2 : State → SepProp} {φ : State → Prop} {Q Qp : State → SepProp → Prop}
    (htr : TraceVRegsEq s s0) (hinv : Inv s.mem)
    (h1 : SepWPp prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2 sm)) (PanicAllocPost s))
    (hfocus : P = P1 ∗ F := by sep_focus)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → Inv sm.mem → φ sm →
      SepWPp prog ret sm (P2 sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hfocus, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hφ, hent⟩ | ⟨hpan_s, P_m, hmm, hp⟩ | ⟨_, hoom⟩⟩ :=
    h1 (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P2 sm ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ := h2 sm hpcm hrunm (hInv_kf hinv hsteps.keepsFrozen)
      hφ R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · have hm' : sm.mem ⊨ (P_m ∗ F) ∗ R := by rw [sepConj_assoc]; exact hmm
    have halloc := hp (F ∗ R) hmm
    rw [sepConj_assoc, satisfies_pure_sepConj] at halloc
    have halloc0 : allocFailedIn s0 sm ∧ s0.trace <+: sm.trace := by
      simpa [allocFailedIn, htr.1] using halloc.1
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_s, P_m ∗ F, hm', hpan sm (P_m ∗ F) halloc0⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem signalMessageNew_seg3_seq_wp_placed_gen' {Inv : Memory → Prop}
    (hInv_kf : ∀ {m m'}, Inv m → Memory.KeepsFrozen m m' → Inv m')
    {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P1 F : SepProp} {P2 : State → SepProp} {φ : State → Prop} {Q Qp : State → SepProp → Prop}
    (hinv : Inv s.mem)
    (h1 : SepWP prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2 sm)))
    (hfocus : P = P1 ∗ F := by sep_focus)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → Inv sm.mem → φ sm →
      SepWPp prog ret sm (P2 sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hfocus, sepConj_assoc] at hm
  rcases h1.elim hm hL with ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hφ, hent⟩ | ⟨_, hoom⟩⟩
  · have hmm' : sm.mem ⊨ (P2 sm ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ := h2 sm hpcm hrunm (hInv_kf hinv hsteps.keepsFrozen)
      hφ R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem new_compute_mac_and_append_wpp_placed_gen [LibsignalPlacement] {Inv : Memory → Prop}
    (hInv_kf : ∀ {m m'}, Inv m → Memory.KeepsFrozen m m' → Inv m')
    {C : Crypto} {A : RustAlloc} {H : LibsignalHooks}
    (hMac : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 60)
      (withMemInv Inv (computeMacSpec C.F A)))
    (x : SignalMessageNewGhost) (sp0 serPtr addrCap : BitVec 64)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32) (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (s : State) (hinv : Inv s.mem)
    (hpc : s.pc = (blkPl_63).base + 988#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64) (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = 32#64) (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = addrCap) (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H) ((blkPl_63).base + 1088#64) s
      (((sp0 - 368#64) ↦₆₄ x.senderIkA) ∗ ((sp0 - 360#64) ↦₆₄ x.receiverIkA) ∗
       ((sp0 - 352#64) ↦₆₄ x.macKeyA) ∗ (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
       (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗ (x.macKeyA ↦ₛ keyToBytes32 x.macKey) ∗
       vecU8At A (sp0 - 176#64)
         (BitVec.ofNat 64 (1 + (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 8))
         serPtr (x.serPrefix6 uuidTryParse) ∗
       memRegion (sp0 - 152#64) 16 ∗ A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧ sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧ sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = addrCap ∧ sm.readReg64 .x24 = x.ret ∧ sm.readReg64 .x26 = serPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = BitVec.ofNat 64 (x.model C.F uuidTryParse).serialized.length ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧ TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 368#64) ↦₆₄ x.senderIkA) ∗ ((sp0 - 360#64) ↦₆₄ x.receiverIkA) ∗
          ((sp0 - 352#64) ↦₆₄ x.macKeyA) ∗ (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
          (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗ (x.macKeyA ↦ₛ keyToBytes32 x.macKey) ∗
          cells (sp0 - 176#64) 3 ∗ memRegion (sp0 - 152#64) 16 ∗
          boxU8Buf A serPtr (x.model C.F uuidTryParse).serialized ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  simp only [arm64_norm] at hx19 hx20 hx21 hx22 hx24 hx25 hx27 hx29
  have hser6_bounds : 36 ≤ (x.serPrefix6 uuidTryParse).length ∧ (x.serPrefix6 uuidTryParse).length < 2 ^ 35 := by
    have ⟨_, _⟩ := encode_protoMsg_length_bounds x hct_bound hpq_bound
    have := serPrefix6_length x; omega
  have htotCap_toNat :
      (BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length + 8#64).toNat =
        (x.serPrefix6 uuidTryParse).length + 8 := by
    rw [← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hser6_toNat : (BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length).toNat = (x.serPrefix6 uuidTryParse).length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hrem8 :
      (BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length + 8#64).toNat -
        (x.serPrefix6 uuidTryParse).length = 8 := by omega
  have h176_8 : sp0 - 176#64 + 8#64 = sp0 - 168#64 := by bv_lin
  have h176_16 : sp0 - 176#64 + 16#64 = sp0 - 160#64 := by bv_lin
  rw [totCap_eq_serLen_add_8 x,
    vecU8At_eq_of_pos A (sp0 - 176#64)
      (BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length + 8#64)
      serPtr (x.serPrefix6 uuidTryParse) (by omega),
    hrem8, memRegion_eight (serPtr + BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length),
    h176_8, h176_16]
  simp only [sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun wmac_dst => ?_
  rw [NewMacAndBoxesCallees.pull_pure_mid9]
  refine SepWPp.pure_elim fun ⟨_, hcap_lt, hserPtr_ne⟩ => ?_
  apply signalMessageNew_of_sepWP_placed_gen hInv_kf (mid := lsmpl.base 60) hinv
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hinv0
  refine signalMessageNew_call_placed_gen hInv_kf
    (x := ⟨sp0 - 152#64, x.senderIkA, x.senderIk, x.receiverIkA, x.receiverIk,
      x.macKeyA, x.macKey, serPtr, x.serPrefix6 uuidTryParse⟩)
    (F := ((sp0 - 368#64) ↦₆₄ x.senderIkA) ∗ ((sp0 - 360#64) ↦₆₄ x.receiverIkA) ∗
          ((sp0 - 352#64) ↦₆₄ x.macKeyA) ∗
          ((sp0 - 176#64) ↦₆₄ (BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length + 8#64)) ∗
          ((sp0 - 168#64) ↦₆₄ serPtr) ∗
          ((sp0 - 160#64) ↦₆₄ BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length) ∗
          A.live serPtr (BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length + 8#64).toNat 1 ∗
          ((serPtr + BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length) ↦₆₄ wmac_dst))
    hinv0 hMac (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
    (by simp only [arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ R' hm => by
      simpa only [computeMacSpec, allocFailedIn, State.trace_setPC, State.trace_writeReg64,
        arm64_norm] using allowPanic_frame id hm) ?_
  · intro R' hm
    simp only [computeMacSpec, sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
    exact ⟨by omega, NewMacAndBoxesCallees.satisfies_of_sep_focus hm (by sep_focus)⟩
  intro sf1 _ hpc1 hrun1 hsp1 hcs1
  rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
  simp only [wp_norm, arm64_norm, *] at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
  simp only [computeMacSpec, okTagVec, bv_sub_add_lit sp0 152 8, sepConj_assoc]
  refine SepWPp.pure_elim fun htr1 => ?_
  simp only [wp_norm, arm64_norm] at htr1
  obtain ⟨macW, hmacW⟩ := exists_unpack64_of_length_8
    (signalMessageNew_computeMac_length C.F x.senderIk x.receiverIk x.macKey (x.serPrefix6 uuidTryParse))
  rw [hmacW, ← pointsTo64_eq_pointsToBytes (sp0 - 144#64) macW]
  apply SepWPp.of_sepWP_ret
  wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
  · rw [model_serialized_length, totCap_eq_serLen_add_8 x]
    simp only [State.spAligned, wp_norm, arm64_norm, *]
  · simp only [hsp, arm64_norm]
    have hbox :
        A.live serPtr (BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length + 8#64).toNat 1 ∗
          ((serPtr ↦ₛ x.serPrefix6 uuidTryParse) ∗
           ((serPtr + BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length) ↦₆₄ macW)) ⊢
        boxU8Buf A serPtr (x.model C.F uuidTryParse).serialized := by
      rw [htotCap_toNat, pointsTo64_eq_pointsToBytes, ← hmacW, ← pointsToBytes_append, ← model_serialized_eq]
      have hlen_ser := model_serialized_length C.F x
      have hser6_len := serPrefix6_length x
      have hne_nil := model_serialized_ne_nil C.F x
      unfold boxU8Buf
      simp only [hne_nil, ↓reduceIte, hser6_len, hlen_ser]
      exact Entails.pure_right ⟨hserPtr_ne, by omega⟩ (Entails.refl _)
    have hcells3 :=
      three_words_entails_cells3 (sp0 - 176#64)
        (BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length + 8#64)
        serPtr (BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length)
    rw [h176_8, h176_16] at hcells3
    have hmem16 :
        ((sp0 - 152#64) ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ ((sp0 - 144#64) ↦₆₄ macW) ⊢
        memRegion (sp0 - 152#64) 16 := by
      rw [memRegion_16_eq_cells2 (sp0 - 152#64), bv_sub_add_lit sp0 152 8]
      exact sepConj_mono (Entails.sepExists_intro 0xFFFFFFFFFFFFFFFE#64) (Entails.sepExists_intro macW)
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono hcells3 (sepConj_mono hmem16 (sepConj_mono_left hbox)))))))))
    exact NewMacAndBoxesCallees.entails_of_sep_focus (by sep_focus)

private theorem new_phase3_wpp_placed_gen [LibsignalPlacement] {Inv : Memory → Prop}
    (hInv_kf : ∀ {m m'}, Inv m → Memory.KeepsFrozen m m' → Inv m')
    {C : Crypto} {A : RustAlloc} {H : LibsignalHooks}
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (h_mc : HookSat H lsMemcpySym framelessMemcpySpec)
    (h_panic : H lsRawVecHandleErrorSym = some Rust.panicked)
    (h_panic2 : H lsAllocHandleErrorSym = some Rust.panicked)
    (hMac : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 60)
      (withMemInv Inv (computeMacSpec C.F A)))
    (x : SignalMessageNewGhost)
    (sp0 serPtr rkPtr ctCopyPtr pqCap pqCopyPtr addrCap : BitVec 64)
    (verW32 : BitVec 32) (hver : verW32.setWidth 8 = x.messageVersion)
    (haddrCap : addrCap = if (x.addresses uuidTryParse).isSome then 36#64 else noneCap)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32) (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (s0 s : State) (hinv : Inv s.mem)
    (hpc : s.pc = (blkPl_63).base + 988#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64) (hsp0 : s0.sp = sp0)
    (hsp0_align : s0.spAligned = true) (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = 32#64) (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = addrCap) (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) (htr : TraceVRegsEq s s0) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H) (s0.readReg64 .lr) s
      (newUnusedPad sp0 ∗ ((sp0 - 408#64) ↦₆₄ rkPtr) ∗ ((sp0 - 400#64) ↦₆₄ x.ciphertextA) ∗
       ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗ ((sp0 - 384#64) ↦₃₂ x.counter) ∗
       ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗ ((sp0 - 376#64) ↦₆₄ x.senderRatchetKeyA) ∗
       ((sp0 - 368#64) ↦₆₄ x.senderIkA) ∗ ((sp0 - 360#64) ↦₆₄ x.receiverIkA) ∗
       ((sp0 - 352#64) ↦₆₄ x.macKeyA) ∗ ((sp0 - 344#64) ↦₆₄ ctCopyPtr) ∗
       ((sp0 - 332#64) ↦₃₂ verW32) ∗ ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
       ((sp0 - 320#64) ↦₆₄ pqCap) ∗ memRegion (sp0 - 312#64) 24 ∗ cells (sp0 - 288#64) 9 ∗
       optSerializeAddressesAt A (sp0 - 216#64) (x.addresses uuidTryParse) ∗
       (∃∗ w192 : BitVec 32, (sp0 - 192#64) ↦₃₂ w192) ∗ (∃∗ w188 : BitVec 32, (sp0 - 188#64) ↦₃₂ w188) ∗
       (∃∗ w184 : BitVec 32, (sp0 - 184#64) ↦₃₂ w184) ∗ (∃∗ w180 : BitVec 32, (sp0 - 180#64) ↦₃₂ w180) ∗
       vecU8At A (sp0 - 176#64)
         (BitVec.ofNat 64 (1 + (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 8))
         serPtr (x.serPrefix6 uuidTryParse) ∗
       memRegion (sp0 - 152#64) 16 ∗ newSavedRegs sp0 s0 ∗
       (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
       (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
       (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
       (x.macKeyA ↦ₛ keyToBytes32 x.macKey) ∗ (x.ciphertextA ↦ₛ x.ciphertext) ∗
       (x.pqRatchetA ↦ₛ x.pqRatchet) ∗ boxU8Buf A rkPtr x.senderRatchetKey.serialize ∗
       boxU8Buf A ctCopyPtr x.ciphertext ∗ optPqBuf A pqCap pqCopyPtr x.pqRatchet ∗
       memRegion x.ret 120 ∗ A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sf Pf =>
        (sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) ∧
        (Pf ⊢
          (∃∗ g : SignalMessageGhost, signalMessageAt A g x.ret (x.model C.F uuidTryParse)) ∗
          (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
          (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
          (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
          (x.macKeyA ↦ₛ keyToBytes32 x.macKey) ∗ (x.ciphertextA ↦ₛ x.ciphertext) ∗
          (x.pqRatchetA ↦ₛ x.pqRatchet) ∗ A.pool ∗ stackAt s0.sp signalMessageNewStack))
      (PanicAllocPost s0) := by
  refine signalMessageNew_seg3_seq_wpp' htr
    (new_compute_mac_and_append_wpp_placed_gen hInv_kf hMac x sp0 serPtr addrCap hct_bound hpq_bound s
      hinv hpc hrun hsp hsp_align hx19 hx20 hx21 hx22 hx24 hx25 hx27 hx29)
    (by sep_focus) (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s1 hpc1 hrun1 ⟨hsp1, hsp_align1, hx19_1, hx21_1, hx22_1, hx24_1, hx26_1, hx27_1, hx28_1, hx29_1, htr1⟩
  have htr1' : TraceVRegsEq s1 s0 := htr1.trans htr
  refine signalMessageNew_seg3_seq_wpp' htr1'
    (new_ct_clone_wpp_placed h_shim h_alloc h_mc h_panic2 x sp0 serPtr
      (BitVec.ofNat 64 (x.model C.F uuidTryParse).serialized.length)
      addrCap hct_bound s1 hpc1 hrun1 hsp1 hsp_align1 hx19_1 hx21_1 hx22_1 hx24_1 hx26_1
      hx27_1 hx28_1 hx29_1)
    (by sep_focus) (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, hsp_align2, hx19_2, hx21_2, hx22_2, hx24_2, hx26_2, hx27_2, hx28_2, hx29_2, htr2⟩
  have htr2' : TraceVRegsEq s2 s0 := htr2.trans htr1'
  refine signalMessageNew_seg3_seq_wpp' htr2'
    (new_pq_clone_wpp_placed h_shim h_alloc h_mc h_panic x sp0 serPtr
      (BitVec.ofNat 64 (x.model C.F uuidTryParse).serialized.length)
      (s2.readReg64 .x25) addrCap hpq_bound s2 hpc2 hrun2 hsp2 hsp_align2 hx19_2 hx21_2
      hx22_2 hx24_2 rfl hx26_2 hx27_2 hx28_2 hx29_2)
    (by sep_focus) (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s3 hpc3 hrun3 ⟨hsp3, hsp_align3, hx19_3, hx21_3, hx22_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, htr3⟩
  have htr3' : TraceVRegsEq s3 s0 := htr3.trans htr2'
  refine signalMessageNew_seg3_seq_wp'
    (new_addr_into_boxed_wp_placed x sp0 serPtr (BitVec.ofNat 64 (x.model C.F uuidTryParse).serialized.length)
      (s2.readReg64 .x25) (s3.readReg64 .x23) addrCap haddrCap s3 hpc3 hrun3 hsp3 hsp_align3
      hx19_3 hx21_3 hx22_3 rfl hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3)
    (by sep_focus) ?_
  intro s4 hpc4 hrun4 ⟨hsp4, hsp_align4, hx19_4, hx21_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4, htr4⟩
  have htr4' : TraceVRegsEq s4 s0 := htr4.trans htr3'
  refine signalMessageNew_seg3_seq_wp'
    (new_sret_stores_wp_placed x sp0 serPtr (s2.readReg64 .x25) (s3.readReg64 .x23)
      (s4.readReg64 .x0) (s4.readReg64 .x20) verW32 hver hct_bound hpq_bound s4
      hpc4 hrun4 hsp4 hsp_align4 rfl hx19_4 rfl hx21_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4)
    (by sep_focus) ?_
  intro s5 hpc5 hrun5 ⟨hsp5, hsp_align5, hx19_5, hx21_5, hx29_5, htr5⟩
  have htr5' : TraceVRegsEq s5 s0 := htr5.trans htr4'
  refine signalMessageNew_seg3_seq_wpp' htr5'
    (new_dealloc_rk_and_ct_wpp_placed h_dealloc x sp0 rkPtr ctCopyPtr pqCopyPtr hct_bound s5
      hpc5 hrun5 hsp5 hsp_align5 hx19_5 hx21_5 hx29_5)
    (by sep_focus) (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s6 hpc6 hrun6 ⟨hsp6, hsp_align6, hx20_6, _hx29_6, htr6⟩
  have htr6' : TraceVRegsEq s6 s0 := htr6.trans htr5'
  have hfr := entails_newFrameRest sp0 rkPtr ctCopyPtr pqCopyPtr
    x.counter x.previousCounter verW32
    x.ciphertextA x.senderRatchetKeyA x.senderIkA x.receiverIkA x.macKeyA x.pqRatchetA
  refine SepWPp.fold hfr (by sep_focus) ?_
  refine signalMessageNew_seg3_seq_wpp' htr6'
    (new_dealloc_pq_and_epilogue_wpp_placed h_dealloc x sp0 pqCap pqCopyPtr hpq_bound s0 s6
      hpc6 hrun6 hsp6 hsp0 hsp0_align hsp_align6 hx20_6 htr6')
    (by sep_focus) (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro sf hpcf hrunf ⟨hspf, hcsf, htrf⟩
  refine SepWPp.done hpcf hrunf ⟨⟨hspf, hcsf, htrf⟩, ?_⟩
  exact NewMacAndBoxesCallees.entails_of_sep_focus (by sep_focus)

set_option maxHeartbeats 3200000 in
private theorem signalMessageNew_placed_ok_gen [LibsignalPlacement] {Inv : Memory → Prop}
    (hInv_cl : ∀ {m}, Inv m → LibsignalCodeLoaded lsmpl m)
    (hInv_kf : ∀ {m m'}, Inv m → Memory.KeepsFrozen m m' → Inv m')
    {C : Crypto} {A : RustAlloc} {H : LibsignalHooks}
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (h_mc : HookSat H lsMemcpySym framelessMemcpySpec)
    (h_panic : H lsRawVecHandleErrorSym = some Rust.panicked)
    (h_panic2 : H lsAllocHandleErrorSym = some Rust.panicked)
    (hPk : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec A)))
    (hEncLen : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 108)
      (withLsCodeLoaded lsmpl (encodedLenSpec A)))
    (hVarint : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 10)
      (withLsCodeLoaded lsmpl (encodeVarintSpec A)))
    (hSerAddr : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 61)
      (withLsCodeLoaded lsmpl (serializeAddressesSpec A uuidTryParse)))
    (hMac : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 60)
      (withMemInv Inv (computeMacSpec C.F A))) :
    subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (blkPl_63).base
      (withMemInv Inv (signalMessageNewSpec C.F A uuidTryParse)) := by
  apply signalMessageNew_subroutine_ok_of_sepWPp
    (Ppost := fun x s0 => x.inputsAt A s0.sp ∗
      (∃∗ g : SignalMessageGhost, signalMessageAt A g x.ret (x.model C.F uuidTryParse)) ∗
      A.pool ∗ stackAt s0.sp signalMessageNewStack)
    (fun x s0 sf htr => by simp only [signalMessageNewSpec]; exact Entails.pure_right htr (Entails.refl _))
    (fun _ _ _ => rfl)
  intro x s0 hpc hrun hsp_align
  rw [show (withMemInv Inv (signalMessageNewSpec C.F A uuidTryParse)).pre x s0 =
      ⌜Inv s0.mem⌝ ∗ (signalMessageNewSpec C.F A uuidTryParse).pre x s0 from sepConj_comm _ _]
  simp only [signalMessageNewSpec, SignalMessageNewGhost.inputsAt, sepConj_assoc]
  refine SepWPp.pure_elim fun hcl0 => SepWPp.pure_elim fun ⟨hx0, hx1, hx2, hx3, hloc_ne, hx4, hx5, hx6, hx7, hx8,
    hct_bound, hpq_bound⟩ => ?_
  conv => arg 4; rw [stackAt_signalMessageNewStack_ready s0.sp]; simp only [sepExists_sepConj_right]
  refine SepWPp.exists_elim fun w408 => SepWPp.exists_elim fun w400 => SepWPp.exists_elim fun w392 =>
    SepWPp.exists_elim fun w384 => SepWPp.exists_elim fun w380 => SepWPp.exists_elim fun w376 =>
    SepWPp.exists_elim fun w368 => SepWPp.exists_elim fun w360 => SepWPp.exists_elim fun w352 =>
    SepWPp.exists_elim fun w344 => SepWPp.exists_elim fun w332 => SepWPp.exists_elim fun w328 =>
    SepWPp.exists_elim fun w320 => SepWPp.exists_elim fun w176 => SepWPp.exists_elim fun w168 =>
    SepWPp.exists_elim fun w160 => ?_
  refine signalMessageNew_seg3_seq_wp_placed_gen' hInv_kf hcl0
    (new_prologue_wp_placed x s0.sp w368 w360 w352 w344 w328 w332 s0 hpc hrun rfl hsp_align hx1 hx2 hx4 hx5 hx6 hx7 hx8)
    (by sep_focus) ?_
  intro s1 hpc1 hrun1 hcl1 ⟨hsp1, hsp_align1, hx3_1, hx4_1, hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hx27_1, hx29_1, htr1⟩
  refine signalMessageNew_seg3_seq_wpp_placed_gen' hInv_kf htr1 hcl1
    (new_addr_and_rk_wpp_placed hPk hSerAddr x s0.sp s1 (hInv_cl hcl1) hpc1 hrun1 hsp1 hsp_align1
      (hx3_1.trans hx3) hloc_ne hx4_1 hx19_1 hx20_1 hx22_1 hx23_1 hx24_1 hx25_1 hx27_1 hx29_1)
    (by sep_focus) (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hsp_align2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx27_2, hx29_2, htr2⟩
  have htr2' : TraceVRegsEq s2 s0 := htr2.trans htr1
  refine signalMessageNew_seg3_seq_wpp_placed_gen' hInv_kf htr2' hcl2
    (new_ct_copy_wpp_placed h_shim h_alloc h_mc h_panic x s0.sp (s2.readReg64 .x28) w400 hct_bound s2
      hpc2 hrun2 hsp2 hsp_align2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx27_2 rfl hx29_2)
    (by sep_focus) (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s3 hpc3 hrun3 hcl3 ⟨hsp3, hsp_align3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx27_3, hx28_3, hx29_3, htr3⟩
  have htr3' : TraceVRegsEq s3 s0 := htr3.trans htr2'
  refine signalMessageNew_seg3_seq_wpp_placed_gen' hInv_kf htr3' hcl3
    (new_pq_copy_wpp_placed h_shim h_alloc h_mc h_panic x s0.sp (s2.readReg64 .x28) (s3.readReg64 .x26) hpq_bound s3
      hpc3 hrun3 hsp3 hsp_align3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 rfl hx27_3 hx28_3 hx29_3)
    (by sep_focus) (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s4 hpc4 hrun4 hcl4 ⟨hsp4, hsp_align4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx26_4, hx27_4, hx28_4, hx29_4, htr4⟩
  have htr4' : TraceVRegsEq s4 s0 := htr4.trans htr3'
  refine SepWPp.fold (optSerializeAddressesAt_unpack A (s0.sp - 312#64) x) (by sep_focus) ?_
  conv => arg 4; simp (disch := decide) only [bv_sub_add_lit, Nat.reduceSub, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun addrCap => SepWPp.exists_elim fun addrPtr => SepWPp.exists_elim fun addrLen => ?_
  refine SepWPp.fold (optPqBuf_extract_pin A (s4.readReg64 .x9) (s4.readReg64 .x25) x.pqRatchet) (by sep_focus) ?_
  simp only [sepConj_assoc]; refine SepWPp.pure_elim fun hpq_pin => ?_
  refine SepWPp.fold (optAddrBuf_extract_cap A addrCap addrPtr addrLen (x.addresses uuidTryParse)) (by sep_focus) ?_
  simp only [sepConj_assoc]; refine SepWPp.pure_elim fun haddrCap => ?_
  have hrk_buf : boxU8Buf A (s2.readReg64 .x28) x.senderRatchetKey.serialize =
      signalMessageNew_vecU8Buf A 33#64 (s2.readReg64 .x28) x.senderRatchetKey.serialize := by
    have hlen : x.senderRatchetKey.serialize.length = 33 := publicKey_serialize_length x.senderRatchetKey
    have h := (vecU8Buf_eq_boxU8Buf A (s2.readReg64 .x28) x.senderRatchetKey.serialize (by omega)).symm
    rw [hlen] at h; exact h
  rw [hrk_buf]
  refine signalMessageNew_seg3_seq_wp_placed_gen' hInv_kf hcl4
    (new_store_wire_wp_placed x s0.sp (s2.readReg64 .x28) (s3.readReg64 .x26) (s4.readReg64 .x9) (s4.readReg64 .x25)
      addrCap addrPtr addrLen w376 w320 hct_bound s4 hpc4 hrun4 hsp4 hsp_align4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4
      hx24_4 rfl hx26_4 hx27_4 hx28_4 hx29_4 rfl)
    (by sep_focus) ?_
  intro s5 hpc5 hrun5 hcl5 ⟨hsp5, hsp_align5, hx0_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hx29_5, htr5⟩
  have htr5' : TraceVRegsEq s5 s0 := htr5.trans htr4'
  have hver32 : ((s0.readReg64 .x0).setWidth 32).setWidth 8 = x.messageVersion := by rw [← hx0]; bv_kernel
  have hstep6 : SepWPp ((blkPC_63).rebase (blkPl_63).base H) ((blkPl_63).base + 440#64) s5
      (((s0.sp - 384#64) ↦₃₂ w384) ∗ ((s0.sp - 380#64) ↦₃₂ w380) ∗ ((s0.sp - 332#64) ↦₃₂ (s0.readReg64 .x0).setWidth 32) ∗
       wireSignalMessageAt A (x.mkPins (s2.readReg64 .x28) (s3.readReg64 .x26) (s4.readReg64 .x9) (s4.readReg64 .x25) addrCap addrPtr)
         (s0.sp - 288#64) (x.protoMsg uuidTryParse) ∗
       ((s0.sp - 176#64) ↦₆₄ w176) ∗ ((s0.sp - 168#64) ↦₆₄ w168) ∗ ((s0.sp - 160#64) ↦₆₄ w160) ∗
       A.pool ∗ stackAt (s0.sp - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = s0.sp - 416#64 ∧ sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9) ∧
         sm.readReg64 .x21 = 33#64 ∧ sm.readReg64 .x22 ≠ 0#64 ∧ sm.readReg64 .x23 = 1#64 ∧
         sm.readReg64 .x24 = x.ret ∧ sm.readReg64 .x25 = s4.readReg64 .x25 ∧ sm.readReg64 .x26 = s3.readReg64 .x26 ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧ sm.readReg64 .x28 = s2.readReg64 .x28 ∧
         sm.readReg64 .x29 = s0.sp - 96#64 ∧ TraceVRegsEq sm s5) ∧
        (Pm ⊢
          ((s0.sp - 384#64) ↦₃₂ x.counter) ∗ ((s0.sp - 380#64) ↦₃₂ x.previousCounter) ∗
          ((s0.sp - 332#64) ↦₃₂ (s0.readReg64 .x0).setWidth 32) ∗
          wireSignalMessageAt A (x.mkPins (s2.readReg64 .x28) (s3.readReg64 .x26) (s4.readReg64 .x9) (s4.readReg64 .x25) addrCap addrPtr)
            (s0.sp - 288#64) (x.protoMsg uuidTryParse) ∗
          vecU8At A (s0.sp - 176#64) (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
            (sm.readReg64 .x22) x.serPrefix0 ∗
          A.pool ∗ stackAt (s0.sp - 416#64) computeMacStack))
      (PanicAllocPost s5) := by
    have hshim := subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl)
      (new_shim_placed_ok h_shim (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63))
    have halloc := subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl)
      (new_alloc_placed_ok h_alloc (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63))
    have ho15c := @oom_at_15c_placed _ H h_panic
    have hfit := wireLengthsFit_protoMsg x hct_bound hpq_bound
    have ⟨henc_lo, henc_hi⟩ := encode_protoMsg_length_bounds x hct_bound hpq_bound
    have ⟨h_adds1, h_cmp9, h_tbz, h_hi, h_add9_eq, h_add9_toNat⟩ := encLen_overflow_checks henc_lo henc_hi
    have h_pos9 : 0 < (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9 := by omega
    have h_le9 : (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9 ≤ 9223372036854775807 := by omega
    have hsp0_align : (s0.sp &&& 15#64 == 0#64) = true := by simpa only [State.spAligned, hsp5, arm64_norm] using hsp_align5
    apply signalMessageNew_of_sepWP_placed (mid := lsmpl.base 108) (hInv_cl hcl5); wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun5])
    intro hcl5_0
    refine signalMessageNew_call_placed (x := ⟨s0.sp - 288#64, x.mkPins (s2.readReg64 .x28) (s3.readReg64 .x26) (s4.readReg64 .x9) (s4.readReg64 .x25) addrCap addrPtr, x.protoMsg uuidTryParse⟩)
      (F := ((s0.sp - 384#64) ↦₃₂ w384) ∗ ((s0.sp - 380#64) ↦₃₂ w380) ∗ ((s0.sp - 332#64) ↦₃₂ (s0.readReg64 .x0).setWidth 32) ∗
            ((s0.sp - 176#64) ↦₆₄ w176) ∗ ((s0.sp - 168#64) ↦₆₄ w168) ∗ ((s0.sp - 160#64) ↦₆₄ w160) ∗
            A.pool ∗ memRegion (s0.sp - 416#64 - 4624#64) 4608)
      hcl5_0 hEncLen (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun5])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp5, hsp0_align]) (by simp only [wp_norm, arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he) (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
    · intro R' hm; rw [stackAt_computeMac_to_encodedLen (s0.sp - 416#64)] at hm
      rw [NewEncodeTags123Callees.encodedLenSpec_pre_eq A _ _ (s0.sp - 416#64) (by simp only [wp_norm, arm64_norm, hx0_5]) hfit (by simp only [wp_norm, arm64_norm, hsp5])]
      simp only [State.mem_setPC, State.mem_writeReg64, sepConj_assoc] at hm ⊢; exact NewEncodeTags123Callees.satisfies_of_sep_focus hm (by sep_focus)
    intro sf1 hcl5_1 hpc1 hrun1 hsp1 ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
    simp only [wp_norm, arm64_norm, hsp5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hx29_5]
      at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
    simp only [encodedLenSpec, wp_norm, arm64_norm, hsp5, sepConj_assoc]; refine SepWPp.pure_elim fun ⟨hx0_1, htr1_c⟩ => ?_
    apply signalMessageNew_of_sepWP_placed (mid := lsρ lsRustNoAllocShimSym) hcl5_1; wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1])
    intro hcl5_2
    refine signalMessageNew_call_placed (x := ())
      (F := wireSignalMessageAt A (x.mkPins (s2.readReg64 .x28) (s3.readReg64 .x26) (s4.readReg64 .x9) (s4.readReg64 .x25) addrCap addrPtr) (s0.sp - 288#64) (x.protoMsg uuidTryParse) ∗
            stackAt (s0.sp - 416#64) encodedLenStack ∗ ((s0.sp - 384#64) ↦₃₂ x.counter) ∗ ((s0.sp - 380#64) ↦₃₂ x.previousCounter) ∗
            ((s0.sp - 332#64) ↦₃₂ (s0.readReg64 .x0).setWidth 32) ∗ ((s0.sp - 176#64) ↦₆₄ w176) ∗ ((s0.sp - 168#64) ↦₆₄ w168) ∗ ((s0.sp - 160#64) ↦₆₄ w160) ∗
            A.pool ∗ memRegion (s0.sp - 416#64 - 4624#64) 4608)
      hcl5_2 hshim (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align]) (by simp only [wp_norm, arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he) (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
    · intro R' hm; simp only [noAllocShimSpec, sepConj_assoc, emp_sepConj, State.mem_setMem] at hm ⊢
      exact NewEncodeTags123Callees.satisfies_of_sep_focus hm (by sep_focus)
    intro sf2 hcl5_3 hpc2 hrun2 hsp2 ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
    simp only [wp_norm, arm64_norm, hsp1, h19_1, h21_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1]
      at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
    simp only [noAllocShimSpec]; refine SepWPp.pure_elim fun htr2_c => ?_; simp only [wp_norm, arm64_norm, htr1_c] at htr2_c
    apply signalMessageNew_of_sepWP_placed (mid := lsρ lsRustAllocSym) hcl5_3; wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun2])
    intro hcl5_4
    refine signalMessageNew_call_placed (x := ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9, 1))
      (F := wireSignalMessageAt A (x.mkPins (s2.readReg64 .x28) (s3.readReg64 .x26) (s4.readReg64 .x9) (s4.readReg64 .x25) addrCap addrPtr) (s0.sp - 288#64) (x.protoMsg uuidTryParse) ∗
            ((s0.sp - 384#64) ↦₃₂ x.counter) ∗ ((s0.sp - 380#64) ↦₃₂ x.previousCounter) ∗ ((s0.sp - 332#64) ↦₃₂ (s0.readReg64 .x0).setWidth 32) ∗
            ((s0.sp - 176#64) ↦₆₄ w176) ∗ ((s0.sp - 168#64) ↦₆₄ w168) ∗ ((s0.sp - 160#64) ↦₆₄ w160) ∗
            memRegion (s0.sp - 416#64 - 4624#64) 528)
      hcl5_4 halloc (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun2])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp2, hsp0_align]) (by simp only [wp_norm, arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he) (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
    · intro R' hm; rw [NewEncodeTags123Callees.h4608_split s0.sp] at hm
      rw [NewEncodeTags123Callees.rustAllocSpec_pre_eq A _ _ (s0.sp - 416#64) (by simp only [wp_norm, arm64_norm, h_add9_toNat])
            (by simp only [wp_norm, arm64_norm]) h_pos9 h_le9 (by simp only [wp_norm, arm64_norm, hsp2]),
          NewEncodeTags123Callees.stackAt_allocHook_eq s0.sp]
      simp only [State.mem_setPC, State.mem_writeReg64, sepConj_assoc] at hm ⊢; exact NewEncodeTags123Callees.satisfies_of_sep_focus hm (by sep_focus)
    intro sf3 hcl5_5 hpc3 hrun3 hsp3 ⟨h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, hfp_3⟩
    simp only [wp_norm, arm64_norm, hsp2, h19_2, h20_2, h21_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2]
      at hsp3 h19_3 h20_3 h21_3 h22_3 h23_3 h24_3 h25_3 h26_3 h27_3 h28_3 hfp_3
    by_cases hoom : sf3.readReg64 .x0 = 0#64
    · have hoom0 : (sf3.readReg64 .x0 = 0) = True := eq_true hoom
      simp only [rustAllocSpec, hoom0, ↓reduceIte, pull_pure_alloc_oom]; refine SepWPp.pure_elim fun htr3_c => ?_
      simp only [wp_norm, arm64_norm, htr2_c] at htr3_c; apply SepWPp.of_sepWP (mid := (blkPl_63).base + 348#64); wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun3])
      exact ho15c (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun3]) (by simp only [wp_norm, arm64_norm, htr3_c])
    · have hoom0 : (sf3.readReg64 .x0 = 0) = False := eq_false hoom
      simp only [rustAllocSpec, hoom0, ↓reduceIte, pull_pure_alloc_ok]; refine SepWPp.pure_elim fun ⟨_halign_ptr, htr3_c⟩ => ?_
      simp only [wp_norm, arm64_norm, htr2_c] at htr3_c
      have hoom_beq : (sf3.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
      simp only [arm64_norm] at hoom hoom_beq
      rw [memRegion_split_one (sf3.readReg64 (Reg.gpr 0#5)) ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9) (by omega) (by omega)]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]; refine SepWPp.exists_elim fun _b0 => ?_
      apply signalMessageNew_of_sepWP_placed (mid := lsmpl.base 108) hcl5_5; wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun3])
      intro hcl5_6
      refine signalMessageNew_call_placed (x := ⟨s0.sp - 288#64, x.mkPins (s2.readReg64 .x28) (s3.readReg64 .x26) (s4.readReg64 .x9) (s4.readReg64 .x25) addrCap addrPtr, x.protoMsg uuidTryParse⟩)
        (F := A.live (sf3.readReg64 (Reg.gpr 0#5)) ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9) 1 ∗
              ((sf3.readReg64 (Reg.gpr 0#5)) ↦₈ versionByte x.messageVersion) ∗
              memRegion (sf3.readReg64 (Reg.gpr 0#5) + 1#64) ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 8) ∗
              A.pool ∗ ((s0.sp - 384#64) ↦₃₂ x.counter) ∗ ((s0.sp - 380#64) ↦₃₂ x.previousCounter) ∗ ((s0.sp - 332#64) ↦₃₂ (s0.readReg64 .x0).setWidth 32) ∗
              ((s0.sp - 176#64) ↦₆₄ BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9)) ∗
              ((s0.sp - 168#64) ↦₆₄ sf3.readReg64 (Reg.gpr 0#5)) ∗ ((s0.sp - 160#64) ↦₆₄ 1#64) ∗
              memRegion (s0.sp - 416#64 - 4624#64) 4608)
        hcl5_6 hEncLen (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun3])
        (by simp only [State.spAligned, wp_norm, arm64_norm, hsp3, hsp0_align]) (by simp only [wp_norm, arm64_norm]; rfl) ?_
        (fun _ _ _ _ he => not_satisfies_false_sepConj he) (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
      · intro R' hm
        have hv : BitVec.zeroExtend 8 (4#64 ||| BitVec.zeroExtend 64 (((s0.readReg64 .x0).setWidth 32) <<< 4)) = versionByte x.messageVersion := by
          have _ := hx20_5; rw [← hver32]; unfold versionByte currentVersion; bv_kernel
        rw [NewEncodeTags123Callees.encodedLenSpec_pre_eq A _ _ (s0.sp - 416#64) (by simp only [wp_norm, arm64_norm]) hfit (by simp only [wp_norm, arm64_norm, hsp3])]
        simp only [wp_norm, arm64_norm, hsp2] at hm; rw [NewEncodeTags123Callees.stackAt_allocHook_eq s0.sp, hv] at hm; rw [NewEncodeTags123Callees.h4608_split s0.sp]
        simp only [sepConj_assoc] at hm ⊢; exact NewEncodeTags123Callees.satisfies_of_sep_focus hm (by sep_focus)
      intro sf4 _ hpc4 hrun4 hsp4 ⟨h19_4, h20_4, h21_4, h22_4, h23_4, h24_4, h25_4, h26_4, h27_4, h28_4, hfp_4⟩
      simp only [wp_norm, arm64_norm, hsp3, h19_3, h20_3, h21_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, hfp_3]
        at hsp4 h19_4 h20_4 h21_4 h22_4 h23_4 h24_4 h25_4 h26_4 h27_4 h28_4 hfp_4
      simp only [encodedLenSpec, wp_norm, arm64_norm, hsp3, htr3_c, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hx0_4, htr4_c⟩ => ?_; apply SepWPp.of_sepWP_ret; wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun4]) ⟨?_, ?_⟩
      · simp only [wp_norm, arm64_norm, hsp4, hsp0_align, h19_4, h20_4, h21_4, h22_4, ne_eq, eq_false hoom,
          not_false_eq_true, h23_4, h24_4, h25_4, h26_4, h27_4, h28_4, hfp_4, htr4_c, and_self]
      · rw [stackAt_computeMac_to_encodedLen (s0.sp - 416#64)]; unfold SignalMessageNewGhost.serPrefix0
        simp only [wp_norm, arm64_norm, h22_4]
        rw [← pack_serPrefix0 A s0.sp (sf3.readReg64 (Reg.gpr 0#5)) x.messageVersion
              (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length henc_lo henc_hi hoom]
        simp only [sepConj_assoc]; exact NewEncodeTags123Callees.entails_of_sep_focus (by sep_focus)
  refine signalMessageNew_seg3_seq_wpp_placed_gen' hInv_kf htr5' hcl5 hstep6
    (by sep_focus) (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s6 hpc6 hrun6 hcl6 ⟨hsp6, hsp_align6, hx19_6, hx20_6, hx21_6, hx22_6, _hx23_6, hx24_6, hx25_6, hx26_6, hx27_6, hx28_6, hx29_6, htr6⟩
  have htr6' : TraceVRegsEq s6 s0 := htr6.trans htr5'
  refine signalMessageNew_seg3_seq_wpp_placed_gen' hInv_kf htr6' hcl6
    (new_encode_tag1_wpp_placed h_mc hVarint x s0.sp (s2.readReg64 .x28) (s3.readReg64 .x26)
      (s4.readReg64 .x9) (s4.readReg64 .x25) addrCap addrPtr (s6.readReg64 .x22)
      hct_bound hpq_bound hx22_6 s6 (hInv_cl hcl6) hpc6 hrun6 hsp6 hsp_align6 hx19_6 hx20_6
      hx21_6 rfl hx24_6 hx25_6 hx26_6 hx27_6 hx28_6 hx29_6)
    (by sep_focus) (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s7 hpc7 hrun7 hcl7 ⟨hsp7, hsp_align7, hx19_7, hx20_7, hx21_7, hx22_7, hx23_7, hx24_7, hx25_7, hx26_7, hx27_7, hx28_7, hx29_7, htr7⟩
  have htr7' : TraceVRegsEq s7 s0 := htr7.trans htr6'
  refine signalMessageNew_seg3_seq_wpp_placed_gen' hInv_kf htr7' hcl7
    (new_encode_tag2_wpp_placed hVarint x s0.sp (s2.readReg64 .x28) (s3.readReg64 .x26)
      (s4.readReg64 .x25) (s6.readReg64 .x22) hct_bound hpq_bound hx22_6 s7
      (hInv_cl hcl7) hpc7 hrun7 hsp7 hsp_align7 hx19_7 hx20_7 hx21_7 hx22_7 hx23_7 hx24_7 hx25_7 hx26_7 hx27_7 hx28_7 hx29_7)
    (by sep_focus) (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s8 hpc8 hrun8 hcl8 ⟨hsp8, hsp_align8, hx19_8, hx21_8, hx23_8, hx24_8, hx25_8, hx26_8, hx27_8, hx28_8, hx29_8, htr8⟩
  have htr8' : TraceVRegsEq s8 s0 := htr8.trans htr7'
  refine signalMessageNew_seg3_seq_wpp_placed_gen' hInv_kf htr8' hcl8
    (new_encode_tag3_wpp_placed hVarint x s0.sp (s2.readReg64 .x28) (s3.readReg64 .x26)
      (s4.readReg64 .x9) (s4.readReg64 .x25) (s6.readReg64 .x22)
      hct_bound hpq_bound hx22_6 s8 (hInv_cl hcl8) hpc8 hrun8 hsp8 hsp_align8 hx19_8 hx21_8 hx23_8 hx24_8 hx25_8 hx26_8 hx27_8 hx28_8 hx29_8)
    (by sep_focus) (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s9 hpc9 hrun9 hcl9 ⟨hsp9, hsp_align9, hx19_9, hx20_9, hx21_9, hx23_9, hx24_9, hx25_9, hx26_9, hx27_9, hx28_9, hx29_9, htr9⟩
  have htr9' : TraceVRegsEq s9 s0 := htr9.trans htr8'
  refine signalMessageNew_seg3_seq_wpp_placed_gen' hInv_kf htr9' hcl9
    (new_encode_tag4_wpp_placed h_mc hVarint x s0.sp (s2.readReg64 .x28) (s3.readReg64 .x26)
      (s4.readReg64 .x9) (s4.readReg64 .x25) addrCap addrPtr (s6.readReg64 .x22) w392
      hct_bound hpq_bound hx22_6 s9 (hInv_cl hcl9) hpc9 hrun9 hsp9 hsp_align9 hx19_9 hx20_9 hx21_9 hx23_9 hx24_9 hx25_9 hx26_9 hx27_9 hx28_9 hx29_9)
    (by sep_focus) (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s10 hpc10 hrun10 hcl10 ⟨hsp10, hsp_align10, hx19_10, hx20_10, hx21_10, hx23_10, hx24_10, hx25_10, hx26_10, hx27_10, hx28_10, hx29_10, htr10⟩
  have htr10' : TraceVRegsEq s10 s0 := htr10.trans htr9'
  refine signalMessageNew_seg3_seq_wpp_placed_gen' hInv_kf htr10' hcl10
    (new_encode_tag56_wpp_placed h_mc hVarint x s0.sp (s2.readReg64 .x28) (s3.readReg64 .x26)
      (s4.readReg64 .x9) (s4.readReg64 .x25) addrCap addrPtr (s6.readReg64 .x22) w408
      hct_bound hpq_bound hx22_6 hpq_pin haddrCap s10 (hInv_cl hcl10) hpc10 hrun10 hsp10 hsp_align10
      hx19_10 hx20_10 hx21_10 hx23_10 hx24_10 hx25_10 hx26_10 hx27_10 hx28_10 hx29_10)
    (by sep_focus) (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s11 hpc11 hrun11 hcl11 ⟨hsp11, hsp_align11, hx19_11, hx20_11, hx21_11, hx22_11, _hx23_11, hx24_11, hx25_11, hx27_11, hx29_11, htr11⟩
  have htr11' : TraceVRegsEq s11 s0 := htr11.trans htr10'
  refine SepWPp.fold
    (wireSignalMessageAt_unpack_for_phase3 A x s0.sp (s2.readReg64 .x28)
      (s3.readReg64 .x26) (s4.readReg64 .x9) (s4.readReg64 .x25) addrCap addrPtr hct_bound hpq_pin haddrCap)
    (by sep_focus) ?_
  rw [show (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9 =
      1 + (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 8 by omega]
  simp only [sepConj_assoc]
  have hstep8 := new_phase3_wpp_placed_gen hInv_kf h_shim h_alloc h_dealloc h_mc h_panic h_panic2 hMac
    x s0.sp (s6.readReg64 .x22) (s2.readReg64 .x28) (s3.readReg64 .x26) (s4.readReg64 .x9) (s4.readReg64 .x25) addrCap
    ((s0.readReg64 .x0).setWidth 32) hver32 haddrCap hct_bound hpq_bound
    s0 s11 hcl11 hpc11 hrun11 hsp11 rfl hsp_align hsp_align11
    hx19_11 hx20_11 hx21_11 hx22_11 hx24_11 hx25_11 hx27_11 hx29_11 htr11'
  have hfocus :
      (cells (s0.sp - 288#64) 9 ∗ optSerializeAddressesAt A (s0.sp - 216#64) (x.addresses uuidTryParse) ∗
        (∃∗ w192 : BitVec 32, (s0.sp - 192#64) ↦₃₂ w192) ∗ (∃∗ w188 : BitVec 32, (s0.sp - 188#64) ↦₃₂ w188) ∗
        (∃∗ w184 : BitVec 32, (s0.sp - 184#64) ↦₃₂ w184) ∗ (∃∗ w180 : BitVec 32, (s0.sp - 180#64) ↦₃₂ w180) ∗
        boxU8Buf A (s2.readReg64 .x28) x.senderRatchetKey.serialize ∗ boxU8Buf A (s3.readReg64 .x26) x.ciphertext ∗
        optPqBuf A (s4.readReg64 .x9) (s4.readReg64 .x25) x.pqRatchet ∗
        ((s0.sp - 408#64) ↦₆₄ s2.readReg64 .x28) ∗ ((s0.sp - 392#64) ↦₆₄ s4.readReg64 .x25) ∗
        ((s0.sp - 344#64) ↦₆₄ s3.readReg64 .x26) ∗
        vecU8At A (s0.sp - 176#64)
          (BitVec.ofNat 64 (1 + (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 8))
          (s6.readReg64 .x22) (x.serPrefix6 uuidTryParse) ∗
        A.pool ∗ stackAt (s0.sp - 416#64) computeMacStack ∗ ((s0.sp - 320#64) ↦₆₄ s4.readReg64 .x9) ∗
        ((s0.sp - 384#64) ↦₃₂ x.counter) ∗ ((s0.sp - 380#64) ↦₃₂ x.previousCounter) ∗
        ((s0.sp - 332#64) ↦₃₂ (s0.readReg64 .x0).setWidth 32) ∗ ((s0.sp - 376#64) ↦₆₄ x.senderRatchetKeyA) ∗
        memRegion (s0.sp - 312#64) 24 ∗ ((s0.sp - 328#64) ↦₆₄ x.pqRatchetA) ∗
        (x.pqRatchetA ↦ₛ x.pqRatchet) ∗ ((s0.sp - 400#64) ↦₆₄ x.ciphertextA) ∗
        (x.ciphertextA ↦ₛ x.ciphertext) ∗ optAddrAt A x.locA x.loc ∗ protocolAddressAt A x.rem x.remA ∗
        (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗ (s0.sp ↦₆₄ x.ciphertextA) ∗
        ((s0.sp + 8#64) ↦₆₄ BitVec.ofNat 64 x.ciphertext.length) ∗ ((s0.sp + 16#64) ↦₆₄ x.senderIkA) ∗
        ((s0.sp + 24#64) ↦₆₄ x.receiverIkA) ∗ ((s0.sp + 32#64) ↦₆₄ x.pqRatchetA) ∗
        ((s0.sp + 40#64) ↦₆₄ BitVec.ofNat 64 x.pqRatchet.length) ∗
        ((s0.sp - 368#64) ↦₆₄ x.senderIkA) ∗ ((s0.sp - 360#64) ↦₆₄ x.receiverIkA) ∗
        ((s0.sp - 352#64) ↦₆₄ x.macKeyA) ∗ newSavedRegs s0.sp s0 ∗ (x.macKeyA ↦ₛ keyToBytes32 x.macKey) ∗
        (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗ (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
        memRegion x.ret 120 ∗ newUnusedPad s0.sp ∗ memRegion (s0.sp - 152#64) 16) =
      (newUnusedPad s0.sp ∗ ((s0.sp - 408#64) ↦₆₄ s2.readReg64 .x28) ∗ ((s0.sp - 400#64) ↦₆₄ x.ciphertextA) ∗
        ((s0.sp - 392#64) ↦₆₄ s4.readReg64 .x25) ∗ ((s0.sp - 384#64) ↦₃₂ x.counter) ∗
        ((s0.sp - 380#64) ↦₃₂ x.previousCounter) ∗ ((s0.sp - 376#64) ↦₆₄ x.senderRatchetKeyA) ∗
        ((s0.sp - 368#64) ↦₆₄ x.senderIkA) ∗ ((s0.sp - 360#64) ↦₆₄ x.receiverIkA) ∗
        ((s0.sp - 352#64) ↦₆₄ x.macKeyA) ∗ ((s0.sp - 344#64) ↦₆₄ s3.readReg64 .x26) ∗
        ((s0.sp - 332#64) ↦₃₂ (s0.readReg64 .x0).setWidth 32) ∗ ((s0.sp - 328#64) ↦₆₄ x.pqRatchetA) ∗
        ((s0.sp - 320#64) ↦₆₄ s4.readReg64 .x9) ∗ memRegion (s0.sp - 312#64) 24 ∗ cells (s0.sp - 288#64) 9 ∗
        optSerializeAddressesAt A (s0.sp - 216#64) (x.addresses uuidTryParse) ∗
        (∃∗ w192 : BitVec 32, (s0.sp - 192#64) ↦₃₂ w192) ∗ (∃∗ w188 : BitVec 32, (s0.sp - 188#64) ↦₃₂ w188) ∗
        (∃∗ w184 : BitVec 32, (s0.sp - 184#64) ↦₃₂ w184) ∗ (∃∗ w180 : BitVec 32, (s0.sp - 180#64) ↦₃₂ w180) ∗
        vecU8At A (s0.sp - 176#64)
          (BitVec.ofNat 64 (1 + (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 8))
          (s6.readReg64 .x22) (x.serPrefix6 uuidTryParse) ∗
        memRegion (s0.sp - 152#64) 16 ∗ newSavedRegs s0.sp s0 ∗
        (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
        (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
        (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
        (x.macKeyA ↦ₛ keyToBytes32 x.macKey) ∗ (x.ciphertextA ↦ₛ x.ciphertext) ∗
        (x.pqRatchetA ↦ₛ x.pqRatchet) ∗ boxU8Buf A (s2.readReg64 .x28) x.senderRatchetKey.serialize ∗
        boxU8Buf A (s3.readReg64 .x26) x.ciphertext ∗ optPqBuf A (s4.readReg64 .x9) (s4.readReg64 .x25) x.pqRatchet ∗
        memRegion x.ret 120 ∗ A.pool ∗ stackAt (s0.sp - 416#64) computeMacStack) ∗
      (optAddrAt A x.locA x.loc ∗ protocolAddressAt A x.rem x.remA ∗ (s0.sp ↦₆₄ x.ciphertextA) ∗
        ((s0.sp + 8#64) ↦₆₄ BitVec.ofNat 64 x.ciphertext.length) ∗ ((s0.sp + 16#64) ↦₆₄ x.senderIkA) ∗
        ((s0.sp + 24#64) ↦₆₄ x.receiverIkA) ∗ ((s0.sp + 32#64) ↦₆₄ x.pqRatchetA) ∗
        ((s0.sp + 40#64) ↦₆₄ BitVec.ofNat 64 x.pqRatchet.length)) := by ac_rfl
  intro R hm hL; rw [hfocus, sepConj_assoc] at hm
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, hregs, hent⟩ | ⟨hpan_s, P_f, hmf, hp⟩ | ⟨_, hoom⟩⟩ := hstep8 _ hm hL
  · have hmf' : sf.mem ⊨ (P_f ∗
        (optAddrAt A x.locA x.loc ∗ protocolAddressAt A x.rem x.remA ∗ (s0.sp ↦₆₄ x.ciphertextA) ∗
          ((s0.sp + 8#64) ↦₆₄ BitVec.ofNat 64 x.ciphertext.length) ∗ ((s0.sp + 16#64) ↦₆₄ x.senderIkA) ∗
          ((s0.sp + 24#64) ↦₆₄ x.receiverIkA) ∗ ((s0.sp + 32#64) ↦₆₄ x.pqRatchetA) ∗
          ((s0.sp + 40#64) ↦₆₄ BitVec.ofNat 64 x.pqRatchet.length))) ∗ R := by rw [sepConj_assoc]; exact hmf
    refine ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, _, hmf', hregs,
      Entails.trans (sepConj_mono_left hent) (Entails.of_eq (by ac_rfl))⟩⟩
  · have hmf' : sf.mem ⊨ (P_f ∗
        (optAddrAt A x.locA x.loc ∗ protocolAddressAt A x.rem x.remA ∗ (s0.sp ↦₆₄ x.ciphertextA) ∗
          ((s0.sp + 8#64) ↦₆₄ BitVec.ofNat 64 x.ciphertext.length) ∗ ((s0.sp + 16#64) ↦₆₄ x.senderIkA) ∗
          ((s0.sp + 24#64) ↦₆₄ x.receiverIkA) ∗ ((s0.sp + 32#64) ↦₆₄ x.pqRatchetA) ∗
          ((s0.sp + 40#64) ↦₆₄ BitVec.ofNat 64 x.pqRatchet.length))) ∗ R := by rw [sepConj_assoc]; exact hmf
    have halloc := hp _ hmf; rw [sepConj_assoc, satisfies_pure_sepConj] at halloc
    exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan_s, _, hmf', panicAllocPost_of_eq halloc.1⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem signalMessageNew_placed_ok [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {H : LibsignalHooks}
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (h_mc : HookSat H lsMemcpySym framelessMemcpySpec)
    (h_panic : H lsRawVecHandleErrorSym = some Rust.panicked)
    (h_panic2 : H lsAllocHandleErrorSym = some Rust.panicked)
    (hPk : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec A)))
    (hEncLen : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 108)
      (withLsCodeLoaded lsmpl (encodedLenSpec A)))
    (hVarint : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 10)
      (withLsCodeLoaded lsmpl (encodeVarintSpec A)))
    (hSerAddr : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 61)
      (withLsCodeLoaded lsmpl (serializeAddressesSpec A uuidTryParse)))
    (hMac : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 60)
      (withLsCodeLoaded lsmpl (computeMacSpec C.F A))) :
    subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (blkPl_63).base
      (withLsCodeLoaded lsmpl (signalMessageNewSpec C.F A uuidTryParse)) :=
  signalMessageNew_placed_ok_gen (Inv := LibsignalCodeLoaded lsmpl)
    (fun h => h) (fun h hkf => h.of_keepsFrozen hkf)
    h_shim h_alloc h_dealloc h_mc h_panic h_panic2 hPk hEncLen hVarint hSerAddr hMac

theorem signalMessageNew_placed_cro_ok [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {H : LibsignalHooks}
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (h_mc : HookSat H lsMemcpySym framelessMemcpySpec)
    (h_panic : H lsRawVecHandleErrorSym = some Rust.panicked)
    (h_panic2 : H lsAllocHandleErrorSym = some Rust.panicked)
    (hPk : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec A)))
    (hEncLen : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 108)
      (withLsCodeLoaded lsmpl (encodedLenSpec A)))
    (hVarint : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 10)
      (withLsCodeLoaded lsmpl (encodeVarintSpec A)))
    (hSerAddr : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 61)
      (withLsCodeLoaded lsmpl (serializeAddressesSpec A uuidTryParse)))
    (hMac : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 60)
      (withLsCodeRoLoaded lsmpl (computeMacSpec C.F A))) :
    subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (blkPl_63).base
      (withLsCodeRoLoaded lsmpl (signalMessageNewSpec C.F A uuidTryParse)) :=
  signalMessageNew_placed_ok_gen (Inv := LibsignalCodeRoLoaded lsmpl)
    (fun h => h.1) (fun h hkf => h.of_keepsFrozen hkf)
    h_shim h_alloc h_dealloc h_mc h_panic h_panic2 hPk hEncLen hVarint hSerAddr hMac

end CryptoVerification.LibsignalTripleRatchet
