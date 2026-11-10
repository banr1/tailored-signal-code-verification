/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.EncodedLenCodeSym
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.FetchChunkedV1
import ProofLib.SepLogic.WPp

/-!
# Verification of `V1State.Chunked.Ct1Sampled::encoded_len` (`0x39890`, `0x68b60`)

Provides reusable `BL` call and option-niche split helpers for chunked `encoded_len` subroutines,
and proves symbolic execution of `V1State.Chunked.Ct1Sampled::encoded_len` (`[local#1, #2]`, 67
instructions).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.ProtoRepr

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1 EncodedLen

local notation "tripleRatchetProgAtExt" => CryptoVerification.LibsignalTripleRatchet.contractProg

theorem pair_fetch_entry {f : BitVec 64 → Option Instr} {a1 a2 entry : BitVec 64}
    (hfn : a1 = entry ∨ a2 = entry) {ins : Instr}
    (h1 : f a1 = some ins) (h2 : f a2 = some ins) : f entry = some ins := by
  rcases hfn with rfl | rfl <;> assumption

theorem pair_fetch_add {f : BitVec 64 → Option Instr} {a1 a2 entry : BitVec 64}
    (hfn : a1 = entry ∨ a2 = entry) {k : Nat} {ins : Instr}
    (h1 : f (a1 + BitVec.ofNat 64 k) = some ins)
    (h2 : f (a2 + BitVec.ofNat 64 k) = some ins) :
    f (entry + BitVec.ofNat 64 k) = some ins := by
  rcases hfn with rfl | rfl <;> assumption

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## 1. Reusable `BL` Call Bridge & Stack / Option Cap Split Helpers -/

theorem fnAddr_bl_target {b : BitVec 64} {H : String → Option (State → State)}
    {caller callee : String} {callerOff calleeOff k : Nat} {disp : BitVec 64}
    (hcaller : libsignalSessionCode.fnOff caller = callerOff)
    (hcallee : libsignalSessionCode.fnOff callee = calleeOff)
    (hk : BitVec.ofNat 64 callerOff + BitVec.ofNat 64 k + disp = BitVec.ofNat 64 calleeOff := by decide) :
    (libsignalSessionCode.rebase b H).fnAddr caller + BitVec.ofNat 64 k + disp =
      (libsignalSessionCode.rebase b H).fnAddr callee := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase, hcaller, hcallee,
    BitVec.add_assoc, BitVec.add_assoc, ← BitVec.add_assoc (BitVec.ofNat 64 callerOff), hk]

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32 ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  zext64_truncate32 ule_zero_64 ult_zero_64 ule_self_64 ult_self_64

/-- Abstracted `BL` call at offset `k` from `entry` to a pinned `encoded_len` callee with
    representation `repr`, pure model `encLen`, and stack requirement `stackSz`. -/
def CallPinnedEncLenAt (prog : Program) (entry : BitVec 64) (k : Nat)
    {Ghost Model : Type} (repr : Ghost → BitVec 64 → Model → SepProp)
    (encLen : Model → Nat) (stackSz : Nat) : Prop :=
  ∀ (ret : BitVec 64) (g : Ghost) (a sp : BitVec 64) (m : Model) (s : State) (F : SepProp)
    (Q Qp : State → SepProp → Prop),
    s.pc = entry + BitVec.ofNat 64 k →
    s.status = .Running →
    s.sp = sp →
    sp &&& 15#64 = 0#64 →
    s.readReg64 .x0 = a →
    encLen m < 2 ^ 64 →
    (∀ sf : State,
      sf.pc = entry + BitVec.ofNat 64 (k + 4) →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (encLen m) →
      EpochEncLenCalleeSaved s sf →
      sf.readReg64 .fp = s.readReg64 .fp →
      SepWPp prog ret sf ((repr g a m ∗ stackAt sp stackSz) ∗ F) Q Qp) →
    SepWPp prog ret s ((repr g a m ∗ stackAt sp stackSz) ∗ F) Q Qp

theorem callPinnedEncLenAt_of_bl
    {prog : Program} {entry calleeAddr : BitVec 64} {k : Nat} {disp : BitVec 64}
    {Ghost Model : Type} {repr : Ghost → BitVec 64 → Model → SepProp}
    {encLen : Model → Nat} {stackSz : Nat} {spec : Spec (PinnedEncLenGhost Ghost Model)}
    (hspec_pre : ∀ x s, spec.pre x s =
      (⌜s.readReg64 .x0 = x.a ∧ encLen x.m < 2 ^ 64⌝ ∗ repr x.g x.a x.m ∗ stackAt s.sp stackSz))
    (hspec_post : ∀ x s0 sf, spec.post x s0 sf =
      (⌜sf.readReg64 .x0 = BitVec.ofNat 64 (encLen x.m) ∧ sf.trace = s0.trace⌝ ∗
        repr x.g x.a x.m ∗ stackAt s0.sp stackSz))
    (hspec_panic : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝)
    (hspec_exit : ∀ x code s0 sf, spec.onExit x code s0 sf = ⌜False⌝)
    (hfetch : prog.fetch (entry + BitVec.ofNat 64 k) =
      some (.bl disp))
    (htarget : entry + BitVec.ofNat 64 k + disp = calleeAddr)
    (hcallee : subroutine_ok prog calleeAddr spec)
    (hspec_oom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    CallPinnedEncLenAt prog entry k repr encLen stackSz := by
  intro ret g a sp m s F Q Qp hpc hrun hsp halign hx0 hbound hcont
  subst hsp
  apply SepWPp.of_sepWP (mid := entry + BitVec.ofNat 64 (k + 4))
  wp_steps
  have hlr_eq : entry + BitVec.ofNat 64 k + 4#64 = entry + BitVec.ofNat 64 (k + 4) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  refine SepWP.call_subroutine_frame (x := ⟨a, g, m⟩) (F := F)
    (ret_pc := entry + BitVec.ofNat 64 (k + 4)) hcallee
    (by simp_all) (by simp_all)
    (by simp only [State.spAligned, beq_iff_eq]; simp_all)
    (by simp_all) ?_ ?_ ?_ ?_ (h_oom := ?_)
  · intro R hm
    rw [hspec_pre]
    simp only [sepConj_assoc, satisfies_pure_sepConj, arm64_norm]
    refine ⟨⟨by simp_all, hbound⟩, ?_⟩
    convert hm using 1
    · ac_rfl
    · rfl
  · intro R' sf _ hpan
    rw [hspec_panic, satisfies_pure_sepConj] at hpan
    exact hpan.1
  · intro R' code sf _ hex
    rw [hspec_exit, satisfies_pure_sepConj] at hex
    exact hex.1
  · intro sf hpc_sf hrun_sf hsp_sf hcs_sf
    rw [hspec_post]
    simp only [arm64_norm] at hsp_sf ⊢
    apply SepWP.weaken_pre (P' := ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (encLen m) ∧ sf.trace = s.trace⌝ ∗
        ((repr g a m ∗ stackAt s.sp stackSz) ∗ F))
    · exact Entails.of_eq (by ac_rfl)
    · apply SepWP.pure_elim
      rintro ⟨hx0_sf, htr_sf⟩
      apply SepWP.done hpc_sf hrun_sf
      have ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, hv⟩ := hcs_sf
      have hcs_saved : EpochEncLenCalleeSaved s sf := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all
      have hfp_sf : sf.readReg64 .fp = s.readReg64 .fp := by
        simp_all
      exact hcont sf hpc_sf hrun_sf hsp_sf htr_sf hx0_sf hcs_saved hfp_sf
  · intro R' sf _ hoom
    rw [hspec_oom] at hoom
    exact (not_satisfies_false_sepConj hoom).elim

theorem stackAt_chunkedEncodedLen_eq (sp : BitVec 64) :
    stackAt sp chunkedEncodedLenStack =
      ∃∗ v32 : BitVec 64, ∃∗ v24 : BitVec 64, ∃∗ v16 : BitVec 64, ∃∗ v8 : BitVec 64,
        ((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
        ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8) ∗
        stackAt (sp - 32#64) polyEncodedLenStack := by
  simp only [stackAt, chunkedEncodedLenStack, chunkedEncodedLenFrame, polyEncodedLenStack]
  have hsplit := ProofLib.memRegion_split_le (sp - BitVec.ofNat 64 (0x20 + 0x10)) 16 48
    (by decide) (by decide)
  have haddr1 : sp - BitVec.ofNat 64 (0x20 + 0x10) = sp - 32#64 - 16#64 := by bv_bits
  have haddr2 : sp - BitVec.ofNat 64 (0x20 + 0x10) + BitVec.ofNat 64 16 = sp - 32#64 := by bv_bits
  rw [hsplit, haddr2, haddr1]
  have hcells : memRegion (sp - 32#64) (48 - 16) =
      ∃∗ v32 : BitVec 64, ∃∗ v24 : BitVec 64, ∃∗ v16 : BitVec 64, ∃∗ v8 : BitVec 64,
        ((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
        ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8) := by
    change memRegion (sp - 32#64) (8 * 4) = _
    rw [memRegion_cells (sp - 32#64) 4 (by decide)]
    cells_unfold
  rw [hcells]
  simp only [sepExists_sepConj_right]
  apply sepProp_eq_of_entails
  · exact Entails.sepExists_elim fun v32 => Entails.sepExists_elim fun v24 =>
      Entails.sepExists_elim fun v16 => Entails.sepExists_elim fun v8 =>
      Entails.sepExists_right v32 (Entails.sepExists_right v24
        (Entails.sepExists_right v16 (Entails.sepExists_right v8 (Entails.of_eq (by ac_rfl)))))
  · exact Entails.sepExists_elim fun v32 => Entails.sepExists_elim fun v24 =>
      Entails.sepExists_elim fun v16 => Entails.sepExists_elim fun v8 =>
      Entails.sepExists_right v32 (Entails.sepExists_right v24
        (Entails.sepExists_right v16 (Entails.sepExists_right v8 (Entails.of_eq (by ac_rfl)))))

/-- First word (`[p]`) of `optCt1SentPBPinnedAt`: `noneCap` when `none`, `g.f3.cap` when `some`. -/
def optCt1SentCap (g : Unchunked5PBGhost) : Option V1State.Unchunked.Ct1Sent → BitVec 64
  | none => noneCap
  | some _ => g.f3.cap

/-- Remainder of `optCt1SentPBPinnedAt` after splitting off `(p ↦₆₄ optCt1SentCap g opt)`. -/
def optCt1SentRest (A : RustAlloc) (g : Unchunked5PBGhost) (p : BitVec 64) :
    Option V1State.Unchunked.Ct1Sent → SepProp
  | none => memRegion (p + 8#64) 120
  | some u =>
    ((p + 8#64) ↦₆₄ g.f3.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.hdr.length) ∗
      vecU8Buf A g.f3.cap g.f3.ptr u.hdr ∗
      vecU8At A (p + 0x18#64) g.f4.cap g.f4.ptr u.es ∗
      vecU8At A (p + 0x30#64) g.f5.cap g.f5.ptr u.ct1 ∗
      optAuthenticatorPBPinnedAt A g.auth (p + 0x48#64) u.auth ∗
      ((p + 0x78#64) ↦₆₄ u.epoch)

theorem optCt1SentPBPinnedAt_eq (A : RustAlloc) (g : Unchunked5PBGhost) (p : BitVec 64)
    (opt : Option V1State.Unchunked.Ct1Sent) :
    optCt1SentPBPinnedAt A g p opt =
      (p ↦₆₄ optCt1SentCap g opt) ∗ optCt1SentRest A g p opt := by
  cases opt with
  | none => rfl
  | some u =>
    simp only [optCt1SentPBPinnedAt, ct1SentPBPinnedAt, unchunked5PinnedAt,
      optCt1SentCap, optCt1SentRest, vecU8At_eq_header_sep_buf A p, vecHeader, sepConj_assoc]

theorem optCt1SentRest_cap_bounds {A : RustAlloc} {g : Unchunked5PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.Ct1Sent} {R : SepProp} {m : Memory}
    (hm : m ⊨ optCt1SentRest A g p opt ∗ R) :
    (optCt1SentCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optCt1SentCap g opt + 1#64 != 0#64) = opt.isSome := by
  cases opt with
  | none => simp [optCt1SentCap, arm64_norm]
  | some u =>
    simp only [optCt1SentRest] at hm
    have hbuf : m ⊨ vecU8Buf A g.f3.cap g.f3.ptr u.hdr ∗
        (((p + 8#64) ↦₆₄ g.f3.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.hdr.length) ∗
         vecU8At A (p + 0x18#64) g.f4.cap g.f4.ptr u.es ∗
         vecU8At A (p + 0x30#64) g.f5.cap g.f5.ptr u.ct1 ∗
         optAuthenticatorPBPinnedAt A g.auth (p + 0x48#64) u.auth ∗
         ((p + 0x78#64) ↦₆₄ u.epoch) ∗ R) := by
      convert hm using 1; ac_rfl
    have ⟨_, hcap⟩ := vecU8Buf_bounds hbuf
    exact ⟨cap_add_one_beq_zero_false hcap, cap_add_one_bne_zero_true hcap⟩

/-- First word (`[p]`) of `optEkSentPBPinnedAt`: `noneCap` when `none`, `g.f3.cap` when `some`. -/
def optEkSentCap (g : Unchunked3PBGhost) : Option V1State.Unchunked.EkSent → BitVec 64
  | none => noneCap
  | some _ => g.f3.cap

/-- Remainder of `optEkSentPBPinnedAt` after splitting off `(p ↦₆₄ optEkSentCap g opt)`. -/
def optEkSentRest (A : RustAlloc) (g : Unchunked3PBGhost) (p : BitVec 64) :
    Option V1State.Unchunked.EkSent → SepProp
  | none => memRegion (p + 8#64) 72
  | some u =>
    ((p + 8#64) ↦₆₄ g.f3.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.dk.length) ∗
      vecU8Buf A g.f3.cap g.f3.ptr u.dk ∗
      optAuthenticatorPBPinnedAt A g.auth (p + 0x18#64) u.auth ∗
      ((p + 0x48#64) ↦₆₄ u.epoch)

theorem optEkSentPBPinnedAt_eq (A : RustAlloc) (g : Unchunked3PBGhost) (p : BitVec 64)
    (opt : Option V1State.Unchunked.EkSent) :
    optEkSentPBPinnedAt A g p opt =
      (p ↦₆₄ optEkSentCap g opt) ∗ optEkSentRest A g p opt := by
  cases opt with
  | none => rfl
  | some u =>
    simp only [optEkSentPBPinnedAt, ekSentPBPinnedAt, unchunked3PinnedAt,
      optEkSentCap, optEkSentRest, vecU8At_eq_header_sep_buf A p, vecHeader, sepConj_assoc]

theorem optEkSentRest_cap_bounds {A : RustAlloc} {g : Unchunked3PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.EkSent} {R : SepProp} {m : Memory}
    (hm : m ⊨ optEkSentRest A g p opt ∗ R) :
    (optEkSentCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optEkSentCap g opt + 1#64 != 0#64) = opt.isSome := by
  cases opt with
  | none => simp [optEkSentCap, arm64_norm]
  | some u =>
    simp only [optEkSentRest] at hm
    have hbuf : m ⊨ vecU8Buf A g.f3.cap g.f3.ptr u.dk ∗
        (((p + 8#64) ↦₆₄ g.f3.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.dk.length) ∗
         optAuthenticatorPBPinnedAt A g.auth (p + 0x18#64) u.auth ∗
         ((p + 0x48#64) ↦₆₄ u.epoch) ∗ R) := by
      convert hm using 1; ac_rfl
    have ⟨_, hcap⟩ := vecU8Buf_bounds hbuf
    exact ⟨cap_add_one_beq_zero_false hcap, cap_add_one_bne_zero_true hcap⟩

/-- First word (`[p]`) of `optPolynomialEncoderPBPinnedAt`: `noneCap` when `none`, `g.pts.cap` when `some`. -/
def optPolyEncCap (g : PolynomialEncoderPBGhost) : Option PolynomialEncoder → BitVec 64
  | none => noneCap
  | some _ => g.pts.cap

/-- Remainder of `optPolynomialEncoderPBPinnedAt` after splitting off `(p ↦₆₄ optPolyEncCap g opt)`. -/
def optPolyEncRest (A : RustAlloc) (g : PolynomialEncoderPBGhost) (p : BitVec 64) :
    Option PolynomialEncoder → SepProp
  | none => memRegion (p + 8#64) 48
  | some pb =>
    ((p + 8#64) ↦₆₄ g.pts.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
      vecVecU8Buf A g.pts.cap g.pts.ptr pb.pts ∗
      vecVecU8PinnedAt A g.polys (p + 24#64) pb.polys ∗
      ((p + 48#64) ↦₃₂ pb.idx) ∗
      memRegion (p + 52#64) 4

theorem optPolynomialEncoderPBPinnedAt_eq (A : RustAlloc) (g : PolynomialEncoderPBGhost) (p : BitVec 64)
    (opt : Option PolynomialEncoder) :
    optPolynomialEncoderPBPinnedAt A g p opt =
      (p ↦₆₄ optPolyEncCap g opt) ∗ optPolyEncRest A g p opt := by
  cases opt with
  | none => rfl
  | some pb =>
    simp only [optPolynomialEncoderPBPinnedAt, polynomialEncoderPBPinnedAt,
      optPolyEncCap, optPolyEncRest, vecVecU8PinnedAt_eq_header_buf A g.pts p, sepConj_assoc]

theorem optPolyEncRest_cap_bounds {A : RustAlloc} {g : PolynomialEncoderPBGhost} {p : BitVec 64}
    {opt : Option PolynomialEncoder} {R : SepProp} {m : Memory}
    (hm : m ⊨ optPolyEncRest A g p opt ∗ R) :
    (optPolyEncCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optPolyEncCap g opt + 1#64 != 0#64) = opt.isSome := by
  cases opt with
  | none => simp [optPolyEncCap, arm64_norm]
  | some pb =>
    simp only [optPolyEncRest] at hm
    have hbuf : m ⊨ vecVecU8Buf A g.pts.cap g.pts.ptr pb.pts ∗
        (((p + 8#64) ↦₆₄ g.pts.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
         vecVecU8PinnedAt A g.polys (p + 24#64) pb.polys ∗
         ((p + 48#64) ↦₃₂ pb.idx) ∗ memRegion (p + 52#64) 4 ∗ R) := by
      convert hm using 1; ac_rfl
    have ⟨_, hcap24⟩ := vecVecU8Buf_bounds hbuf
    have hcap : g.pts.cap.toNat < 2 ^ 63 := by omega
    exact ⟨cap_add_one_beq_zero_false hcap, cap_add_one_bne_zero_true hcap⟩

/-- First word (`[p]`) of `optPolynomialDecoderPBPinnedAt`: `noneCap` when `none`, `g.pts.cap` when `some`. -/
def optPolyDecCap (g : PolynomialDecoderPBGhost) : Option PolynomialDecoder → BitVec 64
  | none => noneCap
  | some _ => g.pts.cap

/-- Remainder of `optPolynomialDecoderPBPinnedAt` after splitting off `(p ↦₆₄ optPolyDecCap g opt)`. -/
def optPolyDecRest (A : RustAlloc) (g : PolynomialDecoderPBGhost) (p : BitVec 64) :
    Option PolynomialDecoder → SepProp
  | none => memRegion (p + 8#64) 32
  | some pb =>
    ((p + 8#64) ↦₆₄ g.pts.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
      vecVecU8Buf A g.pts.cap g.pts.ptr pb.pts ∗
      ((p + 24#64) ↦₃₂ pb.ptsNeeded) ∗
      ((p + 28#64) ↦₃₂ pb.polys) ∗
      ((p + 32#64) ↦₈ boolByte pb.isComplete) ∗
      memRegion (p + 33#64) 7

theorem optPolynomialDecoderPBPinnedAt_eq (A : RustAlloc) (g : PolynomialDecoderPBGhost) (p : BitVec 64)
    (opt : Option PolynomialDecoder) :
    optPolynomialDecoderPBPinnedAt A g p opt =
      (p ↦₆₄ optPolyDecCap g opt) ∗ optPolyDecRest A g p opt := by
  cases opt with
  | none => rfl
  | some pb =>
    simp only [optPolynomialDecoderPBPinnedAt, polynomialDecoderPBPinnedAt,
      optPolyDecCap, optPolyDecRest, vecVecU8PinnedAt_eq_header_buf A g.pts p, sepConj_assoc]

theorem optPolyDecRest_cap_bounds {A : RustAlloc} {g : PolynomialDecoderPBGhost} {p : BitVec 64}
    {opt : Option PolynomialDecoder} {R : SepProp} {m : Memory}
    (hm : m ⊨ optPolyDecRest A g p opt ∗ R) :
    (optPolyDecCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optPolyDecCap g opt + 1#64 != 0#64) = opt.isSome := by
  cases opt with
  | none => simp [optPolyDecCap, arm64_norm]
  | some pb =>
    simp only [optPolyDecRest] at hm
    have hbuf : m ⊨ vecVecU8Buf A g.pts.cap g.pts.ptr pb.pts ∗
        (((p + 8#64) ↦₆₄ g.pts.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
         ((p + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((p + 28#64) ↦₃₂ pb.polys) ∗
         ((p + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (p + 33#64) 7 ∗ R) := by
      convert hm using 1; ac_rfl
    have ⟨_, hcap24⟩ := vecVecU8Buf_bounds hbuf
    have hcap : g.pts.cap.toNat < 2 ^ 63 := by omega
    exact ⟨cap_add_one_beq_zero_false hcap, cap_add_one_bne_zero_true hcap⟩

theorem bv_optMsgField_some {inner tot : Nat}
    (heq : 1 + varintLen (BitVec.ofNat 64 inner) + inner = tot) :
    BitVec.ofNat 64 inner +
      BitVec.ofNat 64 (varintLen (BitVec.ofNat 64 inner)) + 1#64 =
      BitVec.ofNat 64 tot := by
  subst heq
  simp only [← BitVec.ofNat_add]
  congr 1; omega

/-! ## 2. `V1State.Chunked.Ct1Sampled::encoded_len` (`0x39890`, `0x68b60`, 67 insns) -/

theorem callPinnedEncLenAtF_true_of_callPinnedEncLenAt
    {prog : Program} {entry : BitVec 64} {k : Nat}
    {Ghost Model : Type} {repr : Ghost → BitVec 64 → Model → SepProp}
    {encLen : Model → Nat} {stackSz : Nat}
    (h : CallPinnedEncLenAt prog entry k repr encLen stackSz) :
    CallPinnedEncLenAtF (fun _ => True) prog entry k repr encLen stackSz := by
  intro ret g a sp m s F Q Qp hpc hrun hsp halign hx0 hbound hcont
  rw [SepWPpF.iff_sepWPp_true]
  exact h ret g a sp m s F Q Qp hpc hrun hsp halign hx0 hbound fun sf h1 h2 h3 h4 h5 h6 h7 =>
    SepWPpF.iff_sepWPp_true.mp (hcont sf h1 h2 h3 h4 h5 h6 h7)

/-- Entry-point membership for the two identical-structure copies of `chunked::Ct1Sampled::encoded_len`
    (`0x39890`, `0x68b60`). -/
def IsChunkedCt1SampledEntry (b : BitVec 64) (abs : String → Option (State → State))
    (entry : BitVec 64) : Prop :=
  (tripleRatchetProgAtExt b abs).fnAddr chunkedCt1SampledEncodedLenLocal1Name = entry ∨
  (tripleRatchetProgAtExt b abs).fnAddr chunkedCt1SampledEncodedLenLocal2Name = entry

open Lean Elab Tactic in
elab "ct1Sampled_fetches_range " hfn:ident kStart:num kEnd:num : tactic => do
  let offs := #[0x39974, 0x63768]
  let fnOffs := #[
    mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x39974,
    mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x63768
  ]
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  for i in [kStart / 4 : kEnd / 4] do
    let k := 4 * i
    if k != 32 && k != 92 && k != 192 then
      let decs := offs.map fun off =>
        mkIdent (`CryptoVerification.SpqrV1.ProtoRepr |>.str
          s!"spqrChunkedCt1SampledBin_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
      let d0 := decs[0]!; let d1 := decs[1]!
      let f0 := fnOffs[0]!; let f1 := fnOffs[1]!
      let kq := Syntax.mkNumLit (toString k)
      if k == 0 then
        let pf0 := mkIdent (`CryptoVerification.blkPC_179_rebase_fetch_base)
        let pf1 := mkIdent (`CryptoVerification.blkPC_407_rebase_fetch_base)
        evalTactic (← `(tactic|
          have := dualBlockP2_fetch_entry $hfn
            (fun b H => $fetchEntry (b := b) (H := H) $f0 (by decide) $d0)
            (fun b H => $fetchEntry (b := b) (H := H) $f1 (by decide) $d1)
            (fun [LibsignalPlacement] H => $pf0 _ H)
            (fun [LibsignalPlacement] H => $pf1 _ H)))
      else
        let kHex := String.ofList (Nat.toDigits 16 k)
        let pf0 := mkIdent (`CryptoVerification |>.str s!"blkPC_179_rebase_fetch_0x{kHex}")
        let pf1 := mkIdent (`CryptoVerification |>.str s!"blkPC_407_rebase_fetch_0x{kHex}")
        evalTactic (← `(tactic|
          have := dualBlockP2_fetch_add $hfn (k := $kq)
            (fun b H => $fetchAdd (b := b) (H := H) (k := $kq) $f0 (by decide) $d0)
            (fun b H => $fetchAdd (b := b) (H := H) (k := $kq) $f1 (by decide) $d1)
            (fun [LibsignalPlacement] H => $pf0 _ H)
            (fun [LibsignalPlacement] H => $pf1 _ H)))

/-- Unpacked representation of `chunkedCt1SampledPBPinnedAt` with the 3 option `cap` words exposed. -/
def chunkedCt1SampledUnpacked (A : RustAlloc) (g : ChunkedCt1SampledPBGhost)
    (a : BitVec 64) (m : V1State.Chunked.Ct1Sampled) : SepProp :=
  (a ↦₆₄ optCt1SentCap g.uc m.uc) ∗ optCt1SentRest A g.uc a m.uc ∗
    ((a + 128#64) ↦₆₄ optPolyEncCap g.sendingCt1 m.sendingCt1) ∗
    optPolyEncRest A g.sendingCt1 (a + 128#64) m.sendingCt1 ∗
    ((a + 184#64) ↦₆₄ optPolyDecCap g.receivingEk m.receivingEk) ∗
    optPolyDecRest A g.receivingEk (a + 184#64) m.receivingEk

theorem chunkedCt1SampledPBPinnedAt_eq_unpacked (A : RustAlloc) (g : ChunkedCt1SampledPBGhost)
    (a : BitVec 64) (m : V1State.Chunked.Ct1Sampled) :
    chunkedCt1SampledPBPinnedAt A g a m = chunkedCt1SampledUnpacked A g a m := by
  unfold chunkedCt1SampledPBPinnedAt chunkedCt1SampledUnpacked
  rw [optCt1SentPBPinnedAt_eq A g.uc a,
    optPolynomialEncoderPBPinnedAt_eq A g.sendingCt1 (a + 128#64),
    optPolynomialDecoderPBPinnedAt_eq A g.receivingEk (a + 184#64)]
  ac_rfl

theorem chunkedCt1SampledUnpacked_bounds {A : RustAlloc} {g : ChunkedCt1SampledPBGhost}
    {a : BitVec 64} {m : V1State.Chunked.Ct1Sampled} {R : SepProp} {mem : Memory}
    (hm : mem ⊨ chunkedCt1SampledUnpacked A g a m ∗ R) :
    ((optCt1SentCap g.uc m.uc + 1#64 == 0#64) = !m.uc.isSome ∧
     (optCt1SentCap g.uc m.uc + 1#64 != 0#64) = m.uc.isSome) ∧
    ((optPolyEncCap g.sendingCt1 m.sendingCt1 + 1#64 == 0#64) = !m.sendingCt1.isSome ∧
     (optPolyEncCap g.sendingCt1 m.sendingCt1 + 1#64 != 0#64) = m.sendingCt1.isSome) ∧
    ((optPolyDecCap g.receivingEk m.receivingEk + 1#64 == 0#64) = !m.receivingEk.isSome ∧
     (optPolyDecCap g.receivingEk m.receivingEk + 1#64 != 0#64) = m.receivingEk.isSome) := by
  unfold chunkedCt1SampledUnpacked at hm
  have h1 : mem ⊨ optCt1SentRest A g.uc a m.uc ∗
      ((a ↦₆₄ optCt1SentCap g.uc m.uc) ∗
       ((a + 128#64) ↦₆₄ optPolyEncCap g.sendingCt1 m.sendingCt1) ∗
       optPolyEncRest A g.sendingCt1 (a + 128#64) m.sendingCt1 ∗
       ((a + 184#64) ↦₆₄ optPolyDecCap g.receivingEk m.receivingEk) ∗
       optPolyDecRest A g.receivingEk (a + 184#64) m.receivingEk ∗ R) := by
    convert hm using 1; ac_rfl
  have h2 : mem ⊨ optPolyEncRest A g.sendingCt1 (a + 128#64) m.sendingCt1 ∗
      ((a ↦₆₄ optCt1SentCap g.uc m.uc) ∗ optCt1SentRest A g.uc a m.uc ∗
       ((a + 128#64) ↦₆₄ optPolyEncCap g.sendingCt1 m.sendingCt1) ∗
       ((a + 184#64) ↦₆₄ optPolyDecCap g.receivingEk m.receivingEk) ∗
       optPolyDecRest A g.receivingEk (a + 184#64) m.receivingEk ∗ R) := by
    convert hm using 1; ac_rfl
  have h3 : mem ⊨ optPolyDecRest A g.receivingEk (a + 184#64) m.receivingEk ∗
      ((a ↦₆₄ optCt1SentCap g.uc m.uc) ∗ optCt1SentRest A g.uc a m.uc ∗
       ((a + 128#64) ↦₆₄ optPolyEncCap g.sendingCt1 m.sendingCt1) ∗
       optPolyEncRest A g.sendingCt1 (a + 128#64) m.sendingCt1 ∗
       ((a + 184#64) ↦₆₄ optPolyDecCap g.receivingEk m.receivingEk) ∗ R) := by
    convert hm using 1; ac_rfl
  exact ⟨optCt1SentRest_cap_bounds h1, optPolyEncRest_cap_bounds h2, optPolyDecRest_cap_bounds h3⟩

/-- Join point at `+0x0b0` (`176`) of `Ct1Sampled::encoded_len`: steps field 3 (`receiving_ek`)
    and epilogue to `s0.readReg64 .lr`. -/
theorem step_ct1Sampled_f3_ret (Φ : Memory → Prop) [FrozenInv Φ] (prog : Program) (A : RustAlloc)
    (entry : BitVec 64)
    (hfn : IsChunkedCt1SampledEntryP2 prog entry)
    (hbl3 : CallPinnedEncLenAtF Φ prog entry 192
      (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack)
    (g : ChunkedCt1SampledPBGhost) (a sp : BitVec 64) (m : V1State.Chunked.Ct1Sampled)
    (hdec_beq : (optPolyDecCap g.receivingEk m.receivingEk + 1#64 == 0#64) = !m.receivingEk.isSome)
    (hdec_bne : (optPolyDecCap g.receivingEk m.receivingEk + 1#64 != 0#64) = m.receivingEk.isSome)
    (hfit : chunkedCt1SampledPBEncodedLen m < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 176#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx19 : s.readReg64 .x19 = a)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64
      (optCt1SentPBFieldEncodedLen m.uc + optPolynomialEncoderPBFieldEncodedLen m.sendingCt1))
    (hcs : s.readReg64 .x21 = s0.readReg64 .x21 ∧ s.readReg64 .x22 = s0.readReg64 .x22 ∧
           s.readReg64 .x23 = s0.readReg64 .x23 ∧ s.readReg64 .x24 = s0.readReg64 .x24 ∧
           s.readReg64 .x25 = s0.readReg64 .x25 ∧ s.readReg64 .x26 = s0.readReg64 .x26 ∧
           s.readReg64 .x27 = s0.readReg64 .x27 ∧ s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (chunkedCt1SampledUnpacked A g a m ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
      stackAt (sp - 32#64) polyEncodedLenStack) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (chunkedCt1SampledPBEncodedLen m) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPpF Φ prog (s0.readReg64 .lr) s P Q Qp := by
  ct1Sampled_fetches_range hfn 176 264
  rcases hcs with ⟨h21, h22, h23, h24, h25, h26, h27, h28⟩
  subst hP
  cases hrec : m.receivingEk with
  | none =>
    simp only [hrec, Option.isSome_none, Bool.not_false] at hdec_beq hdec_bne
    have htot_eq : optCt1SentPBFieldEncodedLen m.uc + optPolynomialEncoderPBFieldEncodedLen m.sendingCt1 =
        chunkedCt1SampledPBEncodedLen m := by
      unfold chunkedCt1SampledPBEncodedLen
      simp only [hrec, optPolynomialDecoderPBFieldEncodedLen, Nat.add_zero]
    unfold chunkedCt1SampledUnpacked
    apply SepWPpF.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    apply SepWPpF.done (by simp_all) (by simp_all)
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by epochEncLen_cc_close)
  | some dec =>
    simp only [hrec, Option.isSome_some, Bool.not_true] at hdec_beq hdec_bne
    have hdec_fit : polynomialDecoderPBEncodedLen dec < 2 ^ 64 := by
      unfold chunkedCt1SampledPBEncodedLen at hfit
      simp only [hrec, optPolynomialDecoderPBFieldEncodedLen] at hfit
      omega
    have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by
      clear *- halign; bv_bits
    unfold chunkedCt1SampledUnpacked
    apply SepWPpF.of_sepWP (mid := entry + 192#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    have hP_bl : ((((a ↦₆₄ optCt1SentCap g.uc m.uc) ∗ optCt1SentRest A g.uc a m.uc ∗
        ((a + 128#64) ↦₆₄ optPolyEncCap g.sendingCt1 m.sendingCt1) ∗
        optPolyEncRest A g.sendingCt1 (a + 128#64) m.sendingCt1 ∗
        ((a + 184#64) ↦₆₄ optPolyDecCap g.receivingEk m.receivingEk) ∗
        optPolyDecRest A g.receivingEk (a + 184#64) m.receivingEk) ∗
        ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
        stackAt (sp - 32#64) polyEncodedLenStack) ∗ F) =
      ((polynomialDecoderPBPinnedAt A g.receivingEk (a + 184#64) dec ∗
        stackAt (sp - 32#64) polyEncodedLenStack) ∗
        (((a ↦₆₄ optCt1SentCap g.uc m.uc) ∗ optCt1SentRest A g.uc a m.uc ∗
          ((a + 128#64) ↦₆₄ optPolyEncCap g.sendingCt1 m.sendingCt1) ∗
          optPolyEncRest A g.sendingCt1 (a + 128#64) m.sendingCt1 ∗
          ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗ F)) := by
      have hopt := optPolynomialDecoderPBPinnedAt_eq A g.receivingEk (a + 184#64) (some dec)
      simp only [optPolynomialDecoderPBPinnedAt] at hopt
      rw [hrec, hopt]
      ac_rfl
    apply SepWPpF.congr_pre hP_bl
    refine hbl3 (s0.readReg64 .lr) g.receivingEk (a + 184#64) (sp - 32#64) dec _ _ Q Qp
      (by simp_all) (by simp_all) (by simp_all) hsp_sub_align
      (by simp_all) hdec_fit ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hcs2 hfp2
    apply SepWPpF.congr_pre hP_bl.symm
    rcases hcs2 with ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2⟩
    have hf3_eq := bv_optMsgField_some (inner := polynomialDecoderPBEncodedLen dec)
      (tot := optPolynomialDecoderPBFieldEncodedLen (some dec)) rfl
    have htot_fit : optPolynomialDecoderPBFieldEncodedLen (some dec) < 2 ^ 64 := by
      unfold chunkedCt1SampledPBEncodedLen at hfit
      simp only [hrec] at hfit; omega
    have hvlen_lt : varintLen (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen dec)) <
        optPolynomialDecoderPBFieldEncodedLen (some dec) := by
      simp only [optPolynomialDecoderPBFieldEncodedLen]; omega
    have ⟨hule_f3, hule_f3_rev, hult_f3, hsub_f3, hbeq_f3⟩ :=
      cmp_ls_false_of_lt hvlen_lt htot_fit
    have ⟨hadd_tot, hult_tot, hule_tot, _, _⟩ :=
      adds_no_overflow_of_eq
        (a := optPolynomialDecoderPBFieldEncodedLen (some dec))
        (b := optCt1SentPBFieldEncodedLen m.uc + optPolynomialEncoderPBFieldEncodedLen m.sendingCt1)
        (c := chunkedCt1SampledPBEncodedLen m)
        (by unfold chunkedCt1SampledPBEncodedLen; simp only [hrec])
        hfit
    apply SepWPpF.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    apply SepWPpF.done (by simp_all) (by simp_all)
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by epochEncLen_cc_close)

/-- Join point at `+0x05c` (`92`) of `Ct1Sampled::encoded_len` when `m.sendingCt1 = some enc`:
    steps field 2 (`sending_ct1`) to `+0x0b0` (`176`). -/
theorem step_ct1Sampled_f2_some (Φ : Memory → Prop) [FrozenInv Φ] (prog : Program) (A : RustAlloc)
    (entry : BitVec 64)
    (hfn : IsChunkedCt1SampledEntryP2 prog entry)
    (hbl2 : CallPinnedEncLenAtF Φ prog entry 92
      (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack)
    (g : ChunkedCt1SampledPBGhost) (a sp : BitVec 64) (m : V1State.Chunked.Ct1Sampled)
    (enc : PolynomialEncoder) (henc : m.sendingCt1 = some enc)
    (hfit : chunkedCt1SampledPBEncodedLen m < 2 ^ 64)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 92#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a + 128#64)
    (hx19 : s.readReg64 .x19 = a)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 (optCt1SentPBFieldEncodedLen m.uc))
    (hcs : s.readReg64 .x21 = s0.readReg64 .x21 ∧ s.readReg64 .x22 = s0.readReg64 .x22 ∧
           s.readReg64 .x23 = s0.readReg64 .x23 ∧ s.readReg64 .x24 = s0.readReg64 .x24 ∧
           s.readReg64 .x25 = s0.readReg64 .x25 ∧ s.readReg64 .x26 = s0.readReg64 .x26 ∧
           s.readReg64 .x27 = s0.readReg64 .x27 ∧ s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (chunkedCt1SampledUnpacked A g a m ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
      stackAt (sp - 32#64) polyEncodedLenStack) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = entry + 176#64 →
      sf.status = .Running →
      sf.sp = sp - 32#64 →
      sf.trace = s.trace →
      sf.readReg64 .x19 = a →
      sf.readReg64 .x20 = BitVec.ofNat 64
        (optCt1SentPBFieldEncodedLen m.uc + optPolynomialEncoderPBFieldEncodedLen m.sendingCt1) →
      (sf.readReg64 .x21 = s0.readReg64 .x21 ∧ sf.readReg64 .x22 = s0.readReg64 .x22 ∧
       sf.readReg64 .x23 = s0.readReg64 .x23 ∧ sf.readReg64 .x24 = s0.readReg64 .x24 ∧
       sf.readReg64 .x25 = s0.readReg64 .x25 ∧ sf.readReg64 .x26 = s0.readReg64 .x26 ∧
       sf.readReg64 .x27 = s0.readReg64 .x27 ∧ sf.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs sf = calleeSavedVRegs s0) →
      SepWPpF Φ prog ret sf P Q Qp) :
    SepWPpF Φ prog ret s P Q Qp := by
  ct1Sampled_fetches_range hfn 96 144
  rcases hcs with ⟨h21, h22, h23, h24, h25, h26, h27, h28⟩
  subst hP
  have henc_fit : polynomialEncoderPBEncodedLen enc < 2 ^ 64 := by
    unfold chunkedCt1SampledPBEncodedLen at hfit
    simp only [henc, optPolynomialEncoderPBFieldEncodedLen] at hfit
    omega
  have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by
    clear *- halign; bv_bits
  have hP_bl : ((chunkedCt1SampledUnpacked A g a m ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
      stackAt (sp - 32#64) polyEncodedLenStack) ∗ F) =
    ((polynomialEncoderPBPinnedAt A g.sendingCt1 (a + 128#64) enc ∗
      stackAt (sp - 32#64) polyEncodedLenStack) ∗
      (((a ↦₆₄ optCt1SentCap g.uc m.uc) ∗ optCt1SentRest A g.uc a m.uc ∗
        ((a + 184#64) ↦₆₄ optPolyDecCap g.receivingEk m.receivingEk) ∗
        optPolyDecRest A g.receivingEk (a + 184#64) m.receivingEk ∗
        ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗ F)) := by
    unfold chunkedCt1SampledUnpacked
    have hopt := optPolynomialEncoderPBPinnedAt_eq A g.sendingCt1 (a + 128#64) (some enc)
    simp only [optPolynomialEncoderPBPinnedAt] at hopt
    rw [henc, hopt]
    ac_rfl
  apply SepWPpF.congr_pre hP_bl
  refine hbl2 ret g.sendingCt1 (a + 128#64) (sp - 32#64) enc s _ Q Qp
    hpc hrun hsp hsp_sub_align hx0 henc_fit ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hcs1 hfp1
  apply SepWPpF.congr_pre hP_bl.symm
  rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1⟩
  have hf2_eq := bv_optMsgField_some (inner := polynomialEncoderPBEncodedLen enc)
    (tot := optPolynomialEncoderPBFieldEncodedLen (some enc)) rfl
  have htot_fit : optPolynomialEncoderPBFieldEncodedLen (some enc) < 2 ^ 64 := by
    unfold chunkedCt1SampledPBEncodedLen at hfit
    simp only [henc] at hfit; omega
  have hvlen_lt : varintLen (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen enc)) <
      optPolynomialEncoderPBFieldEncodedLen (some enc) := by
    simp only [optPolynomialEncoderPBFieldEncodedLen]; omega
  have ⟨hule_f2, hule_f2_rev, hult_f2, hsub_f2, hbeq_f2⟩ :=
    cmp_ls_false_of_lt hvlen_lt htot_fit
  have h12_fit : optCt1SentPBFieldEncodedLen m.uc +
      optPolynomialEncoderPBFieldEncodedLen (some enc) < 2 ^ 64 := by
    unfold chunkedCt1SampledPBEncodedLen at hfit; simp only [henc] at hfit; omega
  have ⟨hadd_12, hult_12, hule_12, _, _⟩ :=
    adds_no_overflow_of_eq
      (a := optPolynomialEncoderPBFieldEncodedLen (some enc))
      (b := optCt1SentPBFieldEncodedLen m.uc)
      (c := optCt1SentPBFieldEncodedLen m.uc + optPolynomialEncoderPBFieldEncodedLen (some enc))
      (by omega)
      h12_fit
  unfold chunkedCt1SampledUnpacked
  apply SepWPpF.of_sepWP (mid := entry + 176#64)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  exact hnext _ (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1])
    (by simp [arm64_norm, htr1]) (by simp [arm64_norm, h19_1, hx19])
    (by simp [arm64_norm, henc, hadd_12, hf2_eq, h20_1, hx20, hx0_1])
    ⟨by simp [arm64_norm, h21_1, h21], by simp [arm64_norm, h22_1, h22],
     by simp [arm64_norm, h23_1, h23], by simp [arm64_norm, h24_1, h24],
     by simp [arm64_norm, h25_1, h25], by simp [arm64_norm, h26_1, h26],
     by simp [arm64_norm, h27_1, h27], by simp [arm64_norm, h28_1, h28]⟩

/-- Prologue + `m.uc` discriminant check (`+0x000..+0x01c`, `0..28` bytes):
    saves `fp, lr, x20, x19`, sets `x19 := a`, and branches to `entry + 28#64` (`+0x01c`)
    if `m.uc.isSome` or `entry + 148#64` (`+0x094`) if `m.uc = none`. -/
theorem step_ct1Sampled_prologue (Φ : Memory → Prop) [FrozenInv Φ] (prog : Program) (A : RustAlloc)
    (entry : BitVec 64)
    (hfn : IsChunkedCt1SampledEntryP2 prog entry)
    (g : ChunkedCt1SampledPBGhost) (a sp v32 v24 v16 v8 : BitVec 64) (m : V1State.Chunked.Ct1Sampled)
    (huc_beq : (optCt1SentCap g.uc m.uc + 1#64 == 0#64) = !m.uc.isSome)
    (huc_bne : (optCt1SentCap g.uc m.uc + 1#64 != 0#64) = m.uc.isSome)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (hx0 : s.readReg64 .x0 = a)
    (hP : P = (chunkedCt1SampledUnpacked A g a m ∗
      ((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
      ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8) ∗
      stackAt (sp - 32#64) polyEncodedLenStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if m.uc.isSome then entry + 28#64 else entry + 148#64) →
      sm.status = .Running → sm.sp = sp - 32#64 → sm.trace = s.trace →
      sm.readReg64 .x19 = a →
      (sm.readReg64 .x21 = s.readReg64 .x21 ∧ sm.readReg64 .x22 = s.readReg64 .x22 ∧
       sm.readReg64 .x23 = s.readReg64 .x23 ∧ sm.readReg64 .x24 = s.readReg64 .x24 ∧
       sm.readReg64 .x25 = s.readReg64 .x25 ∧ sm.readReg64 .x26 = s.readReg64 .x26 ∧
       sm.readReg64 .x27 = s.readReg64 .x27 ∧ sm.readReg64 .x28 = s.readReg64 .x28 ∧ calleeSavedVRegs sm = calleeSavedVRegs s) →
      SepWPpF Φ prog ret sm
        ((chunkedCt1SampledUnpacked A g a m ∗
          ((sp - 32#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s.readReg64 .lr) ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .x19) ∗
          stackAt (sp - 32#64) polyEncodedLenStack) ∗ F) Q Qp) :
    SepWPpF Φ prog ret s P Q Qp := by
  ct1Sampled_fetches_range hfn 0 28
  subst hP
  cases huc : m.uc with
  | none =>
    simp only [huc, Option.isSome_none, Bool.not_false] at huc_beq huc_bne
    unfold chunkedCt1SampledUnpacked
    apply SepWPpF.of_sepWP (mid := entry + 148#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    exact hnext _ (by simp [arm64_norm, huc]) (by simp [arm64_norm, hrun])
      (by simp [arm64_norm, hsp]) (by simp [arm64_norm]) (by simp [arm64_norm, hx0])
      ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
       by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩
  | some u =>
    simp only [huc, Option.isSome_some, Bool.not_true] at huc_beq huc_bne
    unfold chunkedCt1SampledUnpacked
    apply SepWPpF.of_sepWP (mid := entry + 28#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    exact hnext _ (by simp [arm64_norm, huc]) (by simp [arm64_norm, hrun])
      (by simp [arm64_norm, hsp]) (by simp [arm64_norm]) (by simp [arm64_norm, hx0])
      ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
       by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩

/-- When `m.uc = none`, steps from `entry + 148#64` (`+0x094`) to `entry + 92#64` (`+0x05c`)
    or `entry + 176#64` (`+0x0b0`). -/
theorem step_ct1Sampled_f1_none (Φ : Memory → Prop) [FrozenInv Φ] (prog : Program) (A : RustAlloc)
    (entry : BitVec 64)
    (hfn : IsChunkedCt1SampledEntryP2 prog entry)
    (g : ChunkedCt1SampledPBGhost) (a sp : BitVec 64) (m : V1State.Chunked.Ct1Sampled)
    (huc : m.uc = none)
    (henc_beq : (optPolyEncCap g.sendingCt1 m.sendingCt1 + 1#64 == 0#64) = !m.sendingCt1.isSome)
    (henc_bne : (optPolyEncCap g.sendingCt1 m.sendingCt1 + 1#64 != 0#64) = m.sendingCt1.isSome)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 148#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = a)
    (hcs : s.readReg64 .x21 = s0.readReg64 .x21 ∧ s.readReg64 .x22 = s0.readReg64 .x22 ∧
           s.readReg64 .x23 = s0.readReg64 .x23 ∧ s.readReg64 .x24 = s0.readReg64 .x24 ∧
           s.readReg64 .x25 = s0.readReg64 .x25 ∧ s.readReg64 .x26 = s0.readReg64 .x26 ∧
           s.readReg64 .x27 = s0.readReg64 .x27 ∧ s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (chunkedCt1SampledUnpacked A g a m ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
      stackAt (sp - 32#64) polyEncodedLenStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if m.sendingCt1.isSome then entry + 92#64 else entry + 176#64) →
      sm.status = .Running → sm.sp = sp - 32#64 → sm.trace = s0.trace →
      (m.sendingCt1.isSome = true → sm.readReg64 .x0 = a + 128#64) →
      sm.readReg64 .x19 = a →
      sm.readReg64 .x20 = BitVec.ofNat 64 (optCt1SentPBFieldEncodedLen m.uc) →
      (sm.readReg64 .x21 = s0.readReg64 .x21 ∧ sm.readReg64 .x22 = s0.readReg64 .x22 ∧
       sm.readReg64 .x23 = s0.readReg64 .x23 ∧ sm.readReg64 .x24 = s0.readReg64 .x24 ∧
       sm.readReg64 .x25 = s0.readReg64 .x25 ∧ sm.readReg64 .x26 = s0.readReg64 .x26 ∧
       sm.readReg64 .x27 = s0.readReg64 .x27 ∧ sm.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs sm = calleeSavedVRegs s0) →
      SepWPpF Φ prog ret sm P Q Qp) :
    SepWPpF Φ prog ret s P Q Qp := by
  ct1Sampled_fetches_range hfn 148 176
  rcases hcs with ⟨h21, h22, h23, h24, h25, h26, h27, h28⟩
  subst hP
  cases henc : m.sendingCt1 with
  | none =>
    simp only [henc, Option.isSome_none, Bool.not_false] at henc_beq henc_bne
    unfold chunkedCt1SampledUnpacked
    apply SepWPpF.of_sepWP (mid := entry + 176#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    exact hnext _ (by simp [arm64_norm, henc]) (by simp [arm64_norm, hrun])
      (by simp [arm64_norm, hsp]) (by simp [arm64_norm, htr])
      (by intro h; simp [henc] at h) (by simp [arm64_norm, hx19])
      (by simp [arm64_norm, huc, optCt1SentPBFieldEncodedLen])
      ⟨by simp [arm64_norm, h21], by simp [arm64_norm, h22],
       by simp [arm64_norm, h23], by simp [arm64_norm, h24],
       by simp [arm64_norm, h25], by simp [arm64_norm, h26],
       by simp [arm64_norm, h27], by simp [arm64_norm, h28]⟩
  | some enc =>
    simp only [henc, Option.isSome_some, Bool.not_true] at henc_beq henc_bne
    unfold chunkedCt1SampledUnpacked
    apply SepWPpF.of_sepWP (mid := entry + 92#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    exact hnext _ (by simp [arm64_norm, henc]) (by simp [arm64_norm, hrun])
      (by simp [arm64_norm, hsp]) (by simp [arm64_norm, htr])
      (by intro _; simp [arm64_norm, hx19]) (by simp [arm64_norm, hx19])
      (by simp [arm64_norm, huc, optCt1SentPBFieldEncodedLen])
      ⟨by simp [arm64_norm, h21], by simp [arm64_norm, h22],
       by simp [arm64_norm, h23], by simp [arm64_norm, h24],
       by simp [arm64_norm, h25], by simp [arm64_norm, h26],
       by simp [arm64_norm, h27], by simp [arm64_norm, h28]⟩

theorem step_ct1Sampled_f1_some_post (Φ : Memory → Prop) [FrozenInv Φ] (prog : Program) (A : RustAlloc)
    (entry : BitVec 64)
    (hfn : IsChunkedCt1SampledEntryP2 prog entry)
    (g : ChunkedCt1SampledPBGhost) (a sp : BitVec 64) (m : V1State.Chunked.Ct1Sampled)
    (u : V1State.Unchunked.Ct1Sent) (huc : m.uc = some u)
    (henc_beq : (optPolyEncCap g.sendingCt1 m.sendingCt1 + 1#64 == 0#64) = !m.sendingCt1.isSome)
    (henc_bne : (optPolyEncCap g.sendingCt1 m.sendingCt1 + 1#64 != 0#64) = m.sendingCt1.isSome)
    (hfit : chunkedCt1SampledPBEncodedLen m < 2 ^ 64)
    {ret : BitVec 64} {s0 s2 : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc2 : s2.pc = entry + 36#64) (hrun2 : s2.status = .Running)
    (hsp2 : s2.sp = sp - 32#64) (htr2 : s2.trace = s0.trace)
    (hx0_2 : s2.readReg64 .x0 = BitVec.ofNat 64 (ct1SentPBEncodedLen u))
    (h19_2 : s2.readReg64 .x19 = a)
    (hcs2 : s2.readReg64 .x21 = s0.readReg64 .x21 ∧ s2.readReg64 .x22 = s0.readReg64 .x22 ∧
            s2.readReg64 .x23 = s0.readReg64 .x23 ∧ s2.readReg64 .x24 = s0.readReg64 .x24 ∧
            s2.readReg64 .x25 = s0.readReg64 .x25 ∧ s2.readReg64 .x26 = s0.readReg64 .x26 ∧
            s2.readReg64 .x27 = s0.readReg64 .x27 ∧ s2.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0)
    (hP : P = (chunkedCt1SampledUnpacked A g a m ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
      stackAt (sp - 32#64) polyEncodedLenStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if m.sendingCt1.isSome then entry + 92#64 else entry + 176#64) →
      sm.status = .Running → sm.sp = sp - 32#64 → sm.trace = s0.trace →
      (m.sendingCt1.isSome = true → sm.readReg64 .x0 = a + 128#64) →
      sm.readReg64 .x19 = a →
      sm.readReg64 .x20 = BitVec.ofNat 64 (optCt1SentPBFieldEncodedLen m.uc) →
      (sm.readReg64 .x21 = s0.readReg64 .x21 ∧ sm.readReg64 .x22 = s0.readReg64 .x22 ∧
       sm.readReg64 .x23 = s0.readReg64 .x23 ∧ sm.readReg64 .x24 = s0.readReg64 .x24 ∧
       sm.readReg64 .x25 = s0.readReg64 .x25 ∧ sm.readReg64 .x26 = s0.readReg64 .x26 ∧
       sm.readReg64 .x27 = s0.readReg64 .x27 ∧ sm.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs sm = calleeSavedVRegs s0) →
      SepWPpF Φ prog ret sm P Q Qp) :
    SepWPpF Φ prog ret s2 P Q Qp := by
  ct1Sampled_fetches_range hfn 36 92
  ct1Sampled_fetches_range hfn 168 176
  rcases hcs2 with ⟨h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2⟩
  subst hP
  have hf1_eq := bv_optMsgField_some (inner := ct1SentPBEncodedLen u)
    (tot := optCt1SentPBFieldEncodedLen (some u)) rfl
  have htot_fit : optCt1SentPBFieldEncodedLen (some u) < 2 ^ 64 := by
    unfold chunkedCt1SampledPBEncodedLen at hfit
    simp only [huc] at hfit; omega
  have hvlen_lt : varintLen (BitVec.ofNat 64 (ct1SentPBEncodedLen u)) <
      optCt1SentPBFieldEncodedLen (some u) := by
    simp only [optCt1SentPBFieldEncodedLen]; omega
  have ⟨hule_f1, hule_f1_rev, hult_f1, hsub_f1, hbeq_f1⟩ :=
    cmp_ls_false_of_lt hvlen_lt htot_fit
  cases henc : m.sendingCt1 with
  | none =>
    simp only [henc, Option.isSome_none, Bool.not_false] at henc_beq henc_bne
    unfold chunkedCt1SampledUnpacked
    apply SepWPpF.of_sepWP (mid := entry + 176#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    exact hnext _ (by simp [arm64_norm, henc]) (by simp [arm64_norm, hrun2])
      (by simp [arm64_norm, hsp2]) (by simp [arm64_norm, htr2])
      (by intro h; simp [henc] at h) (by simp [arm64_norm, h19_2])
      (by simp [arm64_norm, huc, hf1_eq, hx0_2])
      ⟨by simp [arm64_norm, h21_2], by simp [arm64_norm, h22_2],
       by simp [arm64_norm, h23_2], by simp [arm64_norm, h24_2],
       by simp [arm64_norm, h25_2], by simp [arm64_norm, h26_2],
       by simp [arm64_norm, h27_2], by simp [arm64_norm, h28_2]⟩
  | some enc =>
    simp only [henc, Option.isSome_some, Bool.not_true] at henc_beq henc_bne
    unfold chunkedCt1SampledUnpacked
    apply SepWPpF.of_sepWP (mid := entry + 92#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    exact hnext _ (by simp [arm64_norm, henc]) (by simp [arm64_norm, hrun2])
      (by simp [arm64_norm, hsp2]) (by simp [arm64_norm, htr2])
      (by intro _; simp [arm64_norm, h19_2]) (by simp [arm64_norm, h19_2])
      (by simp [arm64_norm, huc, hf1_eq, hx0_2])
      ⟨by simp [arm64_norm, h21_2], by simp [arm64_norm, h22_2],
       by simp [arm64_norm, h23_2], by simp [arm64_norm, h24_2],
       by simp [arm64_norm, h25_2], by simp [arm64_norm, h26_2],
       by simp [arm64_norm, h27_2], by simp [arm64_norm, h28_2]⟩

theorem step_ct1Sampled_f1_some (Φ : Memory → Prop) [FrozenInv Φ] (prog : Program) (A : RustAlloc)
    (entry : BitVec 64)
    (hfn : IsChunkedCt1SampledEntryP2 prog entry)
    (hbl1 : CallPinnedEncLenAtF Φ prog entry 32
      (ct1SentPBPinnedAt A) ct1SentPBEncodedLen polyEncodedLenStack)
    (g : ChunkedCt1SampledPBGhost) (a sp : BitVec 64) (m : V1State.Chunked.Ct1Sampled)
    (u : V1State.Unchunked.Ct1Sent) (huc : m.uc = some u)
    (henc_beq : (optPolyEncCap g.sendingCt1 m.sendingCt1 + 1#64 == 0#64) = !m.sendingCt1.isSome)
    (henc_bne : (optPolyEncCap g.sendingCt1 m.sendingCt1 + 1#64 != 0#64) = m.sendingCt1.isSome)
    (hfit : chunkedCt1SampledPBEncodedLen m < 2 ^ 64)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 28#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64) (htr : s.trace = s0.trace)
    (halign : sp &&& 15#64 = 0#64) (hx19 : s.readReg64 .x19 = a)
    (hcs : s.readReg64 .x21 = s0.readReg64 .x21 ∧ s.readReg64 .x22 = s0.readReg64 .x22 ∧
           s.readReg64 .x23 = s0.readReg64 .x23 ∧ s.readReg64 .x24 = s0.readReg64 .x24 ∧
           s.readReg64 .x25 = s0.readReg64 .x25 ∧ s.readReg64 .x26 = s0.readReg64 .x26 ∧
           s.readReg64 .x27 = s0.readReg64 .x27 ∧ s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (chunkedCt1SampledUnpacked A g a m ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
      stackAt (sp - 32#64) polyEncodedLenStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if m.sendingCt1.isSome then entry + 92#64 else entry + 176#64) →
      sm.status = .Running → sm.sp = sp - 32#64 → sm.trace = s0.trace →
      (m.sendingCt1.isSome = true → sm.readReg64 .x0 = a + 128#64) →
      sm.readReg64 .x19 = a →
      sm.readReg64 .x20 = BitVec.ofNat 64 (optCt1SentPBFieldEncodedLen m.uc) →
      (sm.readReg64 .x21 = s0.readReg64 .x21 ∧ sm.readReg64 .x22 = s0.readReg64 .x22 ∧
       sm.readReg64 .x23 = s0.readReg64 .x23 ∧ sm.readReg64 .x24 = s0.readReg64 .x24 ∧
       sm.readReg64 .x25 = s0.readReg64 .x25 ∧ sm.readReg64 .x26 = s0.readReg64 .x26 ∧
       sm.readReg64 .x27 = s0.readReg64 .x27 ∧ sm.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs sm = calleeSavedVRegs s0) →
      SepWPpF Φ prog ret sm P Q Qp) :
    SepWPpF Φ prog ret s P Q Qp := by
  ct1Sampled_fetches_range hfn 28 32
  rcases hcs with ⟨h21, h22, h23, h24, h25, h26, h27, h28⟩
  subst hP
  have hu_fit : ct1SentPBEncodedLen u < 2 ^ 64 := by
    unfold chunkedCt1SampledPBEncodedLen at hfit
    simp only [huc, optCt1SentPBFieldEncodedLen] at hfit
    omega
  have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by
    clear *- halign; bv_bits
  have hP_bl : ((chunkedCt1SampledUnpacked A g a m ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
      stackAt (sp - 32#64) polyEncodedLenStack) ∗ F) =
    ((ct1SentPBPinnedAt A g.uc a u ∗
      stackAt (sp - 32#64) polyEncodedLenStack) ∗
      ((((a + 128#64) ↦₆₄ optPolyEncCap g.sendingCt1 m.sendingCt1) ∗
        optPolyEncRest A g.sendingCt1 (a + 128#64) m.sendingCt1 ∗
        ((a + 184#64) ↦₆₄ optPolyDecCap g.receivingEk m.receivingEk) ∗
        optPolyDecRest A g.receivingEk (a + 184#64) m.receivingEk ∗
        ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗ F)) := by
    unfold chunkedCt1SampledUnpacked
    have hopt := optCt1SentPBPinnedAt_eq A g.uc a (some u)
    simp only [optCt1SentPBPinnedAt] at hopt
    rw [huc, hopt]
    ac_rfl
  apply SepWPpF.of_sepWP (mid := entry + 32#64)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  apply SepWPpF.congr_pre hP_bl
  refine hbl1 ret g.uc a (sp - 32#64) u _ _ Q Qp
    (by simp_all) (by simp_all) (by simp_all) hsp_sub_align
    (by simp_all) hu_fit ?_
  intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hcs2 hfp2
  apply SepWPpF.congr_pre hP_bl.symm
  rcases hcs2 with ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2⟩
  exact step_ct1Sampled_f1_some_post Φ prog A entry hfn g a sp m u huc
    henc_beq henc_bne hfit hpc2 hrun2 hsp2 (by simp_all) hx0_2 (by simp_all)
    ⟨by simp_all, by simp_all, by simp_all, by simp_all,
     by simp_all, by simp_all, by simp_all, by simp_all⟩ rfl hnext

theorem step_ct1Sampled_f1 (Φ : Memory → Prop) [FrozenInv Φ] (prog : Program) (A : RustAlloc)
    (entry : BitVec 64)
    (hfn : IsChunkedCt1SampledEntryP2 prog entry)
    (hbl1 : CallPinnedEncLenAtF Φ prog entry 32
      (ct1SentPBPinnedAt A) ct1SentPBEncodedLen polyEncodedLenStack)
    (g : ChunkedCt1SampledPBGhost) (a sp v32 v24 v16 v8 : BitVec 64) (m : V1State.Chunked.Ct1Sampled)
    (huc_beq : (optCt1SentCap g.uc m.uc + 1#64 == 0#64) = !m.uc.isSome)
    (huc_bne : (optCt1SentCap g.uc m.uc + 1#64 != 0#64) = m.uc.isSome)
    (henc_beq : (optPolyEncCap g.sendingCt1 m.sendingCt1 + 1#64 == 0#64) = !m.sendingCt1.isSome)
    (henc_bne : (optPolyEncCap g.sendingCt1 m.sendingCt1 + 1#64 != 0#64) = m.sendingCt1.isSome)
    (hfit : chunkedCt1SampledPBEncodedLen m < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hP : P = (chunkedCt1SampledUnpacked A g a m ∗
      ((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
      ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8) ∗
      stackAt (sp - 32#64) polyEncodedLenStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if m.sendingCt1.isSome then entry + 92#64 else entry + 176#64) →
      sm.status = .Running →
      sm.sp = sp - 32#64 →
      sm.trace = s.trace →
      (m.sendingCt1.isSome = true → sm.readReg64 .x0 = a + 128#64) →
      sm.readReg64 .x19 = a →
      sm.readReg64 .x20 = BitVec.ofNat 64 (optCt1SentPBFieldEncodedLen m.uc) →
      (sm.readReg64 .x21 = s.readReg64 .x21 ∧ sm.readReg64 .x22 = s.readReg64 .x22 ∧
       sm.readReg64 .x23 = s.readReg64 .x23 ∧ sm.readReg64 .x24 = s.readReg64 .x24 ∧
       sm.readReg64 .x25 = s.readReg64 .x25 ∧ sm.readReg64 .x26 = s.readReg64 .x26 ∧
       sm.readReg64 .x27 = s.readReg64 .x27 ∧ sm.readReg64 .x28 = s.readReg64 .x28 ∧ calleeSavedVRegs sm = calleeSavedVRegs s) →
      SepWPpF Φ prog ret sm
        ((chunkedCt1SampledUnpacked A g a m ∗
          ((sp - 32#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s.readReg64 .lr) ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .x19) ∗
          stackAt (sp - 32#64) polyEncodedLenStack) ∗ F) Q Qp) :
    SepWPpF Φ prog ret s P Q Qp := by
  refine step_ct1Sampled_prologue Φ prog A entry hfn g a sp v32 v24 v16 v8 m
    huc_beq huc_bne hpc hrun hsp halign hx0 hP ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx19_1 hcs1
  cases huc : m.uc with
  | none =>
    simp only [huc, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc1
    exact step_ct1Sampled_f1_none Φ prog A entry hfn g a sp m huc
      henc_beq henc_bne hpc1 hrun1 hsp1 htr1 hx19_1 hcs1 rfl hnext
  | some u =>
    simp only [huc, Option.isSome_some, ↓reduceIte] at hpc1
    exact step_ct1Sampled_f1_some Φ prog A entry hfn hbl1 g a sp m u huc
      henc_beq henc_bne hfit hpc1 hrun1 hsp1 htr1 halign hx19_1 hcs1 rfl hnext

theorem ct1Sampled_entry_pinned_wp_p2 (Φ : Memory → Prop) [FrozenInv Φ] (prog : Program) (A : RustAlloc)
    (entry : BitVec 64)
    (hfn : IsChunkedCt1SampledEntryP2 prog entry)
    (hbl1 : CallPinnedEncLenAtF Φ prog entry 32
      (ct1SentPBPinnedAt A) ct1SentPBEncodedLen polyEncodedLenStack)
    (hbl2 : CallPinnedEncLenAtF Φ prog entry 92
      (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack)
    (hbl3 : CallPinnedEncLenAtF Φ prog entry 192
      (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack) :
    ∀ (x : PinnedEncLenGhost ChunkedCt1SampledPBGhost V1State.Chunked.Ct1Sampled)
      (R : SepProp) (s0 : State), s0.pc = entry → s0.status = .Running →
      (s0.mem ⊨ (chunkedCt1SampledEncodedLenPinnedSpec A).pre x s0 ∗ R) → s0.spAligned = true →
      ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
        SepWPpF Φ prog (s0.readReg64 Reg.lr) s0 P
          (fun sf P_f => ((sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (chunkedCt1SampledEncodedLenPinnedSpec A).post x s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (chunkedCt1SampledEncodedLenPinnedSpec A).onPanic x s0 sf ∗ R)) := by
  intro ⟨a, g, m⟩ R s0 hpc0 hrun hpre hsp
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simp only [State.spAligned, beq_iff_eq] at hsp; exact hsp
  simp only [chunkedCt1SampledEncodedLenPinnedSpec, chunkedCt1SampledPBPinnedAt_eq_unpacked,
    stackAt_chunkedEncodedLen_eq,
    sepExists_sepConj_left, sepExists_sepConj_right,
    satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨v32, v24, v16, v8, ⟨hx0, hfit⟩, hpre⟩
  have ⟨⟨huc_beq, huc_bne⟩, ⟨henc_beq, henc_bne⟩, ⟨hdec_beq, hdec_bne⟩⟩ :=
    chunkedCt1SampledUnpacked_bounds hpre
  refine ⟨(chunkedCt1SampledUnpacked A g a m ∗
      ((s0.sp - 32#64) ↦₆₄ v32) ∗ ((s0.sp - 24#64) ↦₆₄ v24) ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗
      stackAt (s0.sp - 32#64) polyEncodedLenStack) ∗ R, emp,
      by rw [sepConj_emp]; convert hpre using 1; ac_rfl, ?_⟩
  refine step_ct1Sampled_f1 (F := R) Φ prog A entry hfn hbl1 g a s0.sp v32 v24 v16 v8 m
    huc_beq huc_bne henc_beq henc_bne hfit hpc0 hrun rfl halign hx0 rfl ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hcs1
  cases henc : m.sendingCt1 with
  | none =>
    simp only [henc, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc1
    have hx20_1' : s1.readReg64 .x20 = BitVec.ofNat 64
        (optCt1SentPBFieldEncodedLen m.uc + optPolynomialEncoderPBFieldEncodedLen m.sendingCt1) := by
      simp only [henc, optPolynomialEncoderPBFieldEncodedLen, Nat.add_zero, hx20_1]
    refine step_ct1Sampled_f3_ret (F := R) Φ prog A entry hfn hbl3 g a s0.sp m
      hdec_beq hdec_bne hfit hpc1 hrun1 hsp1 halign hx19_1 hx20_1' hcs1 rfl ?_
    intro sf hpcf hrunf hspf htrf hx0_f hcsf
    refine ⟨?_, hspf, hcsf⟩
    intro hm_f; rw [sepConj_emp] at hm_f
    simp only [chunkedCt1SampledEncodedLenPinnedSpec, chunkedCt1SampledPBPinnedAt_eq_unpacked,
      stackAt_chunkedEncodedLen_eq,
      sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, s0.readReg64 .x20, s0.readReg64 .x19,
      ⟨hx0_f, by rw [htrf, htr1]⟩, ?_⟩
    convert hm_f using 1; ac_rfl
  | some enc =>
    simp only [henc, Option.isSome_some, ↓reduceIte, forall_const] at hpc1 hx0_1
    refine step_ct1Sampled_f2_some (F := R) Φ prog A entry hfn hbl2 g a s0.sp m enc henc hfit
      hpc1 hrun1 hsp1 halign hx0_1 hx19_1 hx20_1 hcs1 rfl ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hcs2
    refine step_ct1Sampled_f3_ret (F := R) Φ prog A entry hfn hbl3 g a s0.sp m
      hdec_beq hdec_bne hfit hpc2 hrun2 hsp2 halign hx19_2 hx20_2 hcs2 rfl ?_
    intro sf hpcf hrunf hspf htrf hx0_f hcsf
    refine ⟨?_, hspf, hcsf⟩
    intro hm_f; rw [sepConj_emp] at hm_f
    simp only [chunkedCt1SampledEncodedLenPinnedSpec, chunkedCt1SampledPBPinnedAt_eq_unpacked,
      stackAt_chunkedEncodedLen_eq,
      sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, s0.readReg64 .x20, s0.readReg64 .x19,
      ⟨hx0_f, by rw [htrf, htr2, htr1]⟩, ?_⟩
    convert hm_f using 1; ac_rfl

theorem ct1Sampled_entry_pinned_ok_p2 (prog : Program) (A : RustAlloc)
    (entry : BitVec 64)
    (hfn : IsChunkedCt1SampledEntryP2 prog entry)
    (hbl1 : CallPinnedEncLenAtF (fun _ => True) prog entry 32
      (ct1SentPBPinnedAt A) ct1SentPBEncodedLen polyEncodedLenStack)
    (hbl2 : CallPinnedEncLenAtF (fun _ => True) prog entry 92
      (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack)
    (hbl3 : CallPinnedEncLenAtF (fun _ => True) prog entry 192
      (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack) :
    subroutine_ok prog entry (chunkedCt1SampledEncodedLenPinnedSpec A) :=
  subroutine_ok_of_sepWPpF_true (ct1Sampled_entry_pinned_wp_p2 (fun _ => True) prog A entry hfn hbl1 hbl2 hbl3)

theorem ct1Sampled_entry_pinned_lscl_ok [LibsignalPlacement] (prog : Program) (A : RustAlloc)
    (entry : BitVec 64)
    (hfn : IsChunkedCt1SampledEntryP2 prog entry)
    (hbl1 : CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) prog entry 32
      (ct1SentPBPinnedAt A) ct1SentPBEncodedLen polyEncodedLenStack)
    (hbl2 : CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) prog entry 92
      (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack)
    (hbl3 : CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) prog entry 192
      (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack) :
    subroutine_ok prog entry (withLsCodeLoaded lsmpl (chunkedCt1SampledEncodedLenPinnedSpec A)) :=
  subroutine_ok_of_sepWPpF_lscl (ct1Sampled_entry_pinned_wp_p2 (LibsignalCodeLoaded lsmpl) prog A entry hfn hbl1 hbl2 hbl3)

theorem ct1Sampled_entry_pinned_ok_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) (entry : BitVec 64)
    (hfn : IsChunkedCt1SampledEntry b ext entry)
    (hbl1 : CallPinnedEncLenAt (tripleRatchetProgAtExt b ext) entry 32
      (ct1SentPBPinnedAt A) ct1SentPBEncodedLen polyEncodedLenStack)
    (hbl2 : CallPinnedEncLenAt (tripleRatchetProgAtExt b ext) entry 92
      (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack)
    (hbl3 : CallPinnedEncLenAt (tripleRatchetProgAtExt b ext) entry 192
      (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack) :
    subroutine_ok (tripleRatchetProgAtExt b ext) entry (chunkedCt1SampledEncodedLenPinnedSpec A) :=
  ct1Sampled_entry_pinned_ok_p2 (tripleRatchetProgAtExt b ext) A entry (Or.inl ⟨b, ext, rfl, hfn⟩)
    (callPinnedEncLenAtF_true_of_callPinnedEncLenAt hbl1)
    (callPinnedEncLenAtF_true_of_callPinnedEncLenAt hbl2)
    (callPinnedEncLenAtF_true_of_callPinnedEncLenAt hbl3)

theorem chunkedCt1SampledEncodedLen_ok_of_pinned {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (hpinned : subroutine_ok prog entry (chunkedCt1SampledEncodedLenPinnedSpec A)) :
    subroutine_ok prog entry (chunkedCt1SampledEncodedLenSpec A) := by
  refine subroutine_ok_outcome_intro fun ⟨a, m⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [chunkedCt1SampledEncodedLenSpec, chunkedCt1SampledPBAt_eq_exists_pinned,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome ⟨a, g, m⟩ R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [chunkedCt1SampledEncodedLenSpec, chunkedCt1SampledPBAt_eq_exists_pinned,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨g, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

theorem chunkedCt1SampledEncodedLen_lscl_ok_of_pinned {prog : Program} {entry : BitVec 64}
    {pl : MultiPlacement} {A : RustAlloc}
    (hpinned : subroutine_ok prog entry (withLsCodeLoaded pl (chunkedCt1SampledEncodedLenPinnedSpec A))) :
    subroutine_ok prog entry (withLsCodeLoaded pl (chunkedCt1SampledEncodedLenSpec A)) := by
  refine subroutine_ok_outcome_intro fun ⟨a, m⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [withLsCodeLoaded] at hpre
  simp only [chunkedCt1SampledEncodedLenSpec, chunkedCt1SampledPBAt_eq_exists_pinned,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome ⟨a, g, m⟩ R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded] at hpost ⊢
    simp only [chunkedCt1SampledEncodedLenSpec, chunkedCt1SampledPBAt_eq_exists_pinned,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨g, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

def ChunkedCt1SampledEncodedLenLocal1PinnedOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr chunkedCt1SampledEncodedLenLocal1Name) (chunkedCt1SampledEncodedLenPinnedSpec A)
def ChunkedCt1SampledEncodedLenLocal1OkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr chunkedCt1SampledEncodedLenLocal1Name) (chunkedCt1SampledEncodedLenSpec A)
def ChunkedCt1SampledEncodedLenLocal1PinnedOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr chunkedCt1SampledEncodedLenLocal1Name) (chunkedCt1SampledEncodedLenPinnedSpec A)
def ChunkedCt1SampledEncodedLenLocal1Ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr chunkedCt1SampledEncodedLenLocal1Name) (chunkedCt1SampledEncodedLenSpec A)
def ChunkedCt1SampledEncodedLenLocal2PinnedOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr chunkedCt1SampledEncodedLenLocal2Name) (chunkedCt1SampledEncodedLenPinnedSpec A)
def ChunkedCt1SampledEncodedLenLocal2OkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr chunkedCt1SampledEncodedLenLocal2Name) (chunkedCt1SampledEncodedLenSpec A)
def ChunkedCt1SampledEncodedLenLocal2PinnedOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr chunkedCt1SampledEncodedLenLocal2Name) (chunkedCt1SampledEncodedLenPinnedSpec A)
def ChunkedCt1SampledEncodedLenLocal2Ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr chunkedCt1SampledEncodedLenLocal2Name) (chunkedCt1SampledEncodedLenSpec A)

def ChunkedCt1SampledEncodedLenLocal1PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_179).rebase (blkPl_179).base (Rust.withPanics ext)) (blkPl_179).base (withLsCodeLoaded lsmpl (chunkedCt1SampledEncodedLenPinnedSpec A))
def ChunkedCt1SampledEncodedLenLocal1PlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_179).rebase (blkPl_179).base (Rust.withPanics ext)) (blkPl_179).base (withLsCodeLoaded lsmpl (chunkedCt1SampledEncodedLenSpec A))
def ChunkedCt1SampledEncodedLenLocal1PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  ChunkedCt1SampledEncodedLenLocal1PinnedPlacedOkExt A (tripleRatchetExterns C ctl abs)
def ChunkedCt1SampledEncodedLenLocal1PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  ChunkedCt1SampledEncodedLenLocal1PlacedOkExt A (tripleRatchetExterns C ctl abs)
def ChunkedCt1SampledEncodedLenLocal2PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_407).rebase (blkPl_407).base (Rust.withPanics ext)) (blkPl_407).base (withLsCodeLoaded lsmpl (chunkedCt1SampledEncodedLenPinnedSpec A))
def ChunkedCt1SampledEncodedLenLocal2PlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_407).rebase (blkPl_407).base (Rust.withPanics ext)) (blkPl_407).base (withLsCodeLoaded lsmpl (chunkedCt1SampledEncodedLenSpec A))
def ChunkedCt1SampledEncodedLenLocal2PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  ChunkedCt1SampledEncodedLenLocal2PinnedPlacedOkExt A (tripleRatchetExterns C ctl abs)
def ChunkedCt1SampledEncodedLenLocal2PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  ChunkedCt1SampledEncodedLenLocal2PlacedOkExt A (tripleRatchetExterns C ctl abs)
end CryptoVerification.SpqrV1.ProtoRepr
