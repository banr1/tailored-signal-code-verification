/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.E2E.Record.L1GX.BodyDefs
import LibsignalBinary.Proofs.E2E.Record.L1GX.Leaf.ProstSSGXAtMove
import ProofLib.SepLogic.WPp

/-!
# Loop-exit leaf `deserDExitX_ok`

Proves the `SessionRecord::deserialize` loop-exit path in PQXDH scope, relocating the decoded
344-byte `SessionStructure` into the output `SessionRecord` buffer.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.L1GX.Leaf.DeserDExitX

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.Serialization (CanonRecord CanonSession)
open CryptoVerification.E2E.Record.L1GX CryptoVerification.E2E.Record.L1GX.Leaf.ProstSSGXAtMove
open CryptoVerification.E2E.RecordX (DeserializeScopeP)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem fnOff_deser_dexit :
    libsignalSessionCode.fnOff recDeserializeName = 0x16ed4 := by
  exact CryptoVerification.libsignalSessionCode_fnOff_0x16ed4

private theorem memcpy_ok_dexit {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr recDeserializeName + bv% (ls_off% "memcpy" - 0x16ed4))
      framelessMemcpySpec :=
  framelessMemcpy_ok_at (b := b) (C := C) (ctl := ctl) (abs := abs)
    (name := recDeserializeName) (k := num% (ls_off% "memcpy" - 0x16ed4))
    (by simp only [fnOff_deser_dexit, arm64_norm])

gen_decodes CryptoVerification.libsignalSessionCode_tree dexit
  [0x170c0 → 0x170d0, 0x17128 → 0x17134, 0x171e0,
   0x17228 → 0x17268, 0x1738c → 0x173a8, 0x173b4 → 0x173dc]

private theorem int64_raw_toBitVec_dexit (n : Nat) (h : n < 18446744073709551616) :
    ({ toUInt64 := { toBitVec := { toFin := ⟨n, h⟩ } } } : Int64).toBitVec = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  change n = n % 18446744073709551616
  exact (Nat.mod_eq_of_lt h).symm

attribute [local arm64_norm] int64_raw_toBitVec_dexit

private theorem w0_add_one_ne_zero_dexit {w0 : BitVec 64} (h : w0 ≠ noneCap) :
    w0 + 1#64 ≠ 0#64 := by
  unfold noneCap at h
  bv_omega

private theorem w0_add_one_beq_zero_dexit {w0 : BitVec 64} (h : w0 ≠ noneCap) :
    (w0 + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  exact w0_add_one_ne_zero_dexit h

private def deserSavedAtL_dexit (L : BitVec 64) (s0 : State) : SepProp :=
  ((L + 0x710#64) ↦₆₄ s0.readReg64 .x29) ∗ ((L + 0x718#64) ↦₆₄ s0.readReg64 .x30) ∗
    ((L + 0x720#64) ↦₆₄ s0.readReg64 .x28) ∗ ((L + 0x728#64) ↦₆₄ s0.readReg64 .x27) ∗
    ((L + 0x730#64) ↦₆₄ s0.readReg64 .x26) ∗ ((L + 0x738#64) ↦₆₄ s0.readReg64 .x25) ∗
    ((L + 0x740#64) ↦₆₄ s0.readReg64 .x24) ∗ ((L + 0x748#64) ↦₆₄ s0.readReg64 .x23) ∗
    ((L + 0x750#64) ↦₆₄ s0.readReg64 .x22) ∗ ((L + 0x758#64) ↦₆₄ s0.readReg64 .x21) ∗
    ((L + 0x760#64) ↦₆₄ s0.readReg64 .x20) ∗ ((L + 0x768#64) ↦₆₄ s0.readReg64 .x19)

private theorem deserSaved_eq_atL_dexit (s0 : State) :
    deserSaved s0 = deserSavedAtL_dexit (deserSpL s0.sp) s0 := by
  unfold deserSaved deserSavedAtL_dexit deserSpL
  have h0 : s0.sp - 0x60#64 = s0.sp - 0x770#64 + 0x710#64 := by bv_omega
  rw [h0]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

set_option maxHeartbeats 800000 in
private theorem dexit_sepWP_dexit {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s0 s : State} {L out w0 u0 u1 u2 u3 : BitVec 64} {rest : List (BitVec 8)}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr recDeserializeName + 0x254#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = L)
    (hal : s.spAligned = true)
    (hx29 : s.readReg64 .x29 = L + 0x710#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = 0#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hw0 : w0 ≠ noneCap)
    (hrest : rest.length = 336) :
    SepWP (tripleRatchetProgAt b C ctl abs) (s0.readReg64 .lr) s
      (memRegion (L + 8#64) 336 ∗ memRegion (L + 0x158#64) 336 ∗ memRegion (L + 0x2a8#64) 336 ∗
        ((L + 0x400#64) ↦₆₄ 0#64) ∗
        ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
        ((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗
        ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
        (out ↦₆₄ u0) ∗ ((out + 8#64) ↦₆₄ u1) ∗
        ((out + 0x10#64) ↦₆₄ u2) ∗ ((out + 0x18#64) ↦₆₄ u3) ∗
        memRegion (out + 0x20#64) 336 ∗
        deserSavedAtL_dexit L s0)
      (fun sf P_f =>
        sf.sp = L + 0x770#64 ∧
        sf.trace = s.trace ∧
        CalleeSavedPreserved s0 sf ∧
        P_f = (((L + 8#64) ↦ₛ rest) ∗ ((L + 0x158#64) ↦ₛ rest) ∗ ((L + 0x2a8#64) ↦ₛ rest) ∗
          ((L + 0x400#64) ↦₆₄ 0#64) ∗
          ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
          ((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗
          ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
          (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗
          ((out + 0x10#64) ↦₆₄ 0#64) ∗ ((out + 0x18#64) ↦₆₄ w0) ∗
          ((out + 0x20#64) ↦ₛ rest) ∗
          deserSavedAtL_dexit L s0)) := by
  subst hsp
  have hmemcpy := memcpy_ok_dexit (b := b) (C := C) (ctl := ctl) (abs := abs)
  dsimp only [framelessMemcpySpec] at hmemcpy
  have hw0_ne := w0_add_one_ne_zero_dexit hw0
  have hw0_beq := w0_add_one_beq_zero_dexit hw0
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 492)
    fnOff_deser_dexit (by decide) dexit_decode_0x170c0
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 496)
    fnOff_deser_dexit (by decide) dexit_decode_0x170c4
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 500)
    fnOff_deser_dexit (by decide) dexit_decode_0x170c8
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 504)
    fnOff_deser_dexit (by decide) dexit_decode_0x170cc
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 508)
    fnOff_deser_dexit (by decide) dexit_decode_0x170d0
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 596)
    fnOff_deser_dexit (by decide) dexit_decode_0x17128
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 600)
    fnOff_deser_dexit (by decide) dexit_decode_0x1712c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 604)
    fnOff_deser_dexit (by decide) dexit_decode_0x17130
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 608)
    fnOff_deser_dexit (by decide) dexit_decode_0x17134
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 780)
    fnOff_deser_dexit (by decide) dexit_decode_0x171e0
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 852)
    fnOff_deser_dexit (by decide) dexit_decode_0x17228
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 856)
    fnOff_deser_dexit (by decide) dexit_decode_0x1722c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 860)
    fnOff_deser_dexit (by decide) dexit_decode_0x17230
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 864)
    fnOff_deser_dexit (by decide) dexit_decode_0x17234
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 868)
    fnOff_deser_dexit (by decide) dexit_decode_0x17238
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 872)
    fnOff_deser_dexit (by decide) dexit_decode_0x1723c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 876)
    fnOff_deser_dexit (by decide) dexit_decode_0x17240
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 880)
    fnOff_deser_dexit (by decide) dexit_decode_0x17244
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 884)
    fnOff_deser_dexit (by decide) dexit_decode_0x17248
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 888)
    fnOff_deser_dexit (by decide) dexit_decode_0x1724c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 892)
    fnOff_deser_dexit (by decide) dexit_decode_0x17250
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 896)
    fnOff_deser_dexit (by decide) dexit_decode_0x17254
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 900)
    fnOff_deser_dexit (by decide) dexit_decode_0x17258
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 904)
    fnOff_deser_dexit (by decide) dexit_decode_0x1725c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 908)
    fnOff_deser_dexit (by decide) dexit_decode_0x17260
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 912)
    fnOff_deser_dexit (by decide) dexit_decode_0x17264
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 916)
    fnOff_deser_dexit (by decide) dexit_decode_0x17268
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 1208)
    fnOff_deser_dexit (by decide) dexit_decode_0x1738c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 1212)
    fnOff_deser_dexit (by decide) dexit_decode_0x17390
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 1216)
    fnOff_deser_dexit (by decide) dexit_decode_0x17394
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 1220)
    fnOff_deser_dexit (by decide) dexit_decode_0x17398
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 1224)
    fnOff_deser_dexit (by decide) dexit_decode_0x1739c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 1228)
    fnOff_deser_dexit (by decide) dexit_decode_0x173a0
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 1232)
    fnOff_deser_dexit (by decide) dexit_decode_0x173a4
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 1236)
    fnOff_deser_dexit (by decide) dexit_decode_0x173a8
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 1248)
    fnOff_deser_dexit (by decide) dexit_decode_0x173b4
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 1252)
    fnOff_deser_dexit (by decide) dexit_decode_0x173b8
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 1256)
    fnOff_deser_dexit (by decide) dexit_decode_0x173bc
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 1260)
    fnOff_deser_dexit (by decide) dexit_decode_0x173c0
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 1264)
    fnOff_deser_dexit (by decide) dexit_decode_0x173c4
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 1268)
    fnOff_deser_dexit (by decide) dexit_decode_0x173c8
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 1272)
    fnOff_deser_dexit (by decide) dexit_decode_0x173cc
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 1276)
    fnOff_deser_dexit (by decide) dexit_decode_0x173d0
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 1280)
    fnOff_deser_dexit (by decide) dexit_decode_0x173d4
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 1284)
    fnOff_deser_dexit (by decide) dexit_decode_0x173d8
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := H) (k := 1288)
    fnOff_deser_dexit (by decide) dexit_decode_0x173dc
  dsimp only [tripleRatchetProgAt] at hpc hmemcpy ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr recDeserializeName = entry at *
  examples_hide_fetches
  unfold deserSavedAtL_dexit
  wp_steps
  wp_call hmemcpy (s.sp + 8#64, s.sp + 0x428#64, rest)
  wp_steps
  wp_call hmemcpy (s.sp + 0x2a8#64, s.sp + 8#64, rest)
  wp_steps
  wp_call hmemcpy (s.sp + 0x158#64, s.sp + 0x2a8#64, rest)
  wp_steps
  wp_call hmemcpy (out + 0x20#64, s.sp + 0x158#64, rest)
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *], ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [wp_norm, arm64_norm, *]
  · ac_rfl

private theorem sliceCursorAfter_nil_dexit (L p : BitVec 64) (bs : List (BitVec 8)) :
    Prost.sliceCursorAfter (L + 0x3f8#64) p bs [] =
      ((L + 0x3f8#64) ↦₆₄ (p + BitVec.ofNat 64 bs.length)) ∗
        ((L + 0x400#64) ↦₆₄ 0#64) ∗ (p ↦ₛ bs) := by
  unfold Prost.sliceCursorAfter
  have h : L + 0x3f8#64 + 8#64 = L + 0x400#64 := by bv_omega
  rw [h, List.length_nil, Nat.sub_zero]

private theorem memRegion_3f8_split_dexit (L : BitVec 64) :
    memRegion L 0x3f8 =
      memRegion L 8 ∗
        (memRegion (L + 8#64) 336 ∗ memRegion (L + 0x158#64) 336 ∗
          memRegion (L + 0x2a8#64) 336) := by
  rw [memRegion_split' (b := L) (b' := L + 8#64) (N := 0x3f8) (n := 8) (k := 1008)
        (by decide) rfl (by decide),
      memRegion_split' (b := L + 8#64) (b' := L + 0x158#64) (N := 1008) (n := 336) (k := 672)
        (by decide) (by bv_omega) (by decide),
      memRegion_split' (b := L + 0x158#64) (b' := L + 0x2a8#64) (N := 672) (n := 336) (k := 336)
        (by decide) (by bv_omega) (by decide)]

private theorem memRegion_out_split_dexit (out : BitVec 64) :
    memRegion out 368 =
      ∃∗ u3 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        (out ↦₆₄ u0) ∗ ((out + 8#64) ↦₆₄ u1) ∗
          ((out + 0x10#64) ↦₆₄ u2) ∗ ((out + 0x18#64) ↦₆₄ u3) ∗
          memRegion (out + 0x20#64) 336 := by
  rw [memRegion_split' (b := out) (b' := out + 8#64) (N := 368) (n := 8) (k := 360)
        (by decide) rfl (by decide),
      memRegion_split' (b := out + 8#64) (b' := out + 0x10#64) (N := 360) (n := 8) (k := 352)
        (by decide) (by bv_omega) (by decide),
      memRegion_split' (b := out + 0x10#64) (b' := out + 0x18#64) (N := 352) (n := 8) (k := 344)
        (by decide) (by bv_omega) (by decide),
      memRegion_split' (b := out + 0x18#64) (b' := out + 0x20#64) (N := 344) (n := 8) (k := 336)
        (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_eight out, ProofLib.memRegion_eight (out + 8#64),
      ProofLib.memRegion_eight (out + 0x10#64), ProofLib.memRegion_eight (out + 0x18#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

private theorem satisfies_memRegion_out_split_dexit {m : Memory} {out : BitVec 64} {R : SepProp}
    (h : m ⊨ memRegion out 368 ∗ R) :
    ∃ u0 u1 u2 u3 : BitVec 64,
      m ⊨ ((out ↦₆₄ u0) ∗ ((out + 8#64) ↦₆₄ u1) ∗
        ((out + 0x10#64) ↦₆₄ u2) ∗ ((out + 0x18#64) ↦₆₄ u3) ∗
        memRegion (out + 0x20#64) 336) ∗ R := by
  rw [memRegion_out_split_dexit out] at h
  simp only [sepExists_sepConj_left, satisfies_sepExists] at h
  rcases h with ⟨u3, u2, u1, u0, h⟩
  exact ⟨u0, u1, u2, u3, by simpa only [sepConj_assoc] using h⟩

private theorem satisfies_prostSSGXAt_move_dexit {m : Memory} {L : BitVec 64} {v : SSGX} {R :
    SepProp}
    (h : m ⊨ prostSSGXAt A0 (L + 0x420#64) v ∗ R) :
    ∃ w0 : BitVec 64, ∃ rest : List (BitVec 8), ∃ H : SepProp,
      w0 ≠ noneCap ∧ rest.length = 336 ∧
      (∀ b : BitVec 64, ((b ↦₆₄ w0) ∗ ((b + 8#64) ↦ₛ rest) ∗ H) ⊢ prostSSGXAt A0 b v) ∧
      (m ⊨ (((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗ H) ∗ R) := by
  have h428 : L + 0x420#64 + 8#64 = L + 0x428#64 := by bv_omega
  have hmove_ent := prostSSGXAt_move A0 (L + 0x420#64) v
  rw [h428] at hmove_ent
  have h1 := Satisfies.mono (sepConj_mono_left hmove_ent) h
  simp only [sepExists_sepConj_left, satisfies_sepExists] at h1
  rcases h1 with ⟨w0, rest, H, h1⟩
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at h1
  rcases h1 with ⟨⟨hw0, hrest, hrebuild⟩, h1⟩
  exact ⟨w0, rest, H, hw0, hrest, hrebuild, by simpa only [sepConj_assoc] using h1⟩

private theorem deserSavedAtL_entails_memRegion_dexit (L : BitVec 64) (s0 : State) :
    deserSavedAtL_dexit L s0 ⊢ memRegion (L + 0x710#64) 0x60 := by
  unfold deserSavedAtL_dexit
  refine Entails.trans
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (pointsTo64_entails_memRegion _ _)))))))))))) ?_
  have join (n : Nat) (h : n + 8 ≤ 2 ^ 64) :
      memRegion (L + 0x710#64) n ∗ memRegion (L + BitVec.ofNat 64 (0x710 + n)) 8 =
      memRegion (L + 0x710#64) (n + 8) :=
    (memRegion_split' (b := L + 0x710#64) (b' := L + BitVec.ofNat 64 (0x710 + n))
      (n := n) (k := 8) rfl (by bv_omega) h).symm
  simp only [← sepConj_assoc]
  rw [join 8 (by decide), join 16 (by decide), join 24 (by decide),
      join 32 (by decide), join 40 (by decide), join 48 (by decide),
      join 56 (by decide), join 64 (by decide), join 72 (by decide),
      join 80 (by decide), join 88 (by decide)]
  exact Entails.refl _

private theorem dexit_locals_entails_memRegion_dexit (L c0 w0 : BitVec 64) (s0 : State)
    (rest : List (BitVec 8)) (hrest : rest.length = 336) :
    memRegion L 8 ∗
      ((L + 8#64) ↦ₛ rest) ∗ ((L + 0x158#64) ↦ₛ rest) ∗ ((L + 0x2a8#64) ↦ₛ rest) ∗
      ((L + 0x3f8#64) ↦₆₄ c0) ∗ ((L + 0x400#64) ↦₆₄ 0#64) ∗
      ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
      ((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗
      memRegion (L + 0x578#64) 0x170 ∗
      ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
      memRegion (L + 0x6f0#64) 0x20 ∗
      deserSavedAtL_dexit L s0 ⊢
      memRegion L 0x770 := by
  have hb (a : BitVec 64) : (a ↦ₛ rest) ⊢ memRegion a 336 := by
    rw [← hrest]
    exact ProofLib.pointsToBytes_entails_memRegion a rest
  refine Entails.trans
    (sepConj_mono_right
      (sepConj_mono (hb (L + 8#64))
      (sepConj_mono (hb (L + 0x158#64))
      (sepConj_mono (hb (L + 0x2a8#64))
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (hb (L + 0x428#64))
      (sepConj_mono_right
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono_right
        (deserSavedAtL_entails_memRegion_dexit L s0))))))))))))))) ?_
  have join (n k : Nat) (h : n + k ≤ 2 ^ 64) :
      memRegion L n ∗ memRegion (L + BitVec.ofNat 64 n) k = memRegion L (n + k) :=
    (memRegion_split' (b := L) (b' := L + BitVec.ofNat 64 n) (n := n) (k := k) rfl rfl h).symm
  simp only [← sepConj_assoc]
  rw [join 8 336 (by decide), join 344 336 (by decide), join 680 336 (by decide),
      join 1016 8 (by decide), join 1024 8 (by decide), join 1032 8 (by decide),
      join 1040 8 (by decide), join 1048 8 (by decide), join 1056 8 (by decide),
      join 1064 336 (by decide), join 1400 0x170 (by decide), join 1768 8 (by decide),
      join 1776 0x20 (by decide), join 1808 0x60 (by decide)]
  exact Entails.refl _

private theorem dexit_frame_entails_stackAt_dexit (s0 : State) (c0 w0 : BitVec 64)
    (rest : List (BitVec 8)) (hrest : rest.length = 336) :
    let L := deserSpL s0.sp
    stackAt L deserCalleeStack ∗
      (memRegion L 8 ∗
        ((L + 8#64) ↦ₛ rest) ∗ ((L + 0x158#64) ↦ₛ rest) ∗ ((L + 0x2a8#64) ↦ₛ rest) ∗
        ((L + 0x3f8#64) ↦₆₄ c0) ∗ ((L + 0x400#64) ↦₆₄ 0#64) ∗
        ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
        ((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗
        memRegion (L + 0x578#64) 0x170 ∗
        ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
        memRegion (L + 0x6f0#64) 0x20 ∗
        deserSavedAtL_dexit L s0) ⊢
      stackAt s0.sp recDeserializeStack := by
  intro L
  refine Entails.trans
    (sepConj_mono_right (dexit_locals_entails_memRegion_dexit L c0 w0 s0 rest hrest)) ?_
  unfold stackAt
  have h1 : s0.sp - BitVec.ofNat 64 recDeserializeStack = L - BitVec.ofNat 64 deserCalleeStack := by
    dsimp [L, deserSpL, recDeserializeStack, deserCalleeStack]
    bv_omega
  rw [h1,
    memRegion_split' (b := L - BitVec.ofNat 64 deserCalleeStack) (b' := L)
      (N := recDeserializeStack) (n := deserCalleeStack) (k := 0x770) (by decide)
      (by dsimp [deserCalleeStack, recDeserializeStack]; bv_omega)
      (by decide)]
  exact Entails.refl _

theorem deserDExitX_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (x : DeserializeGenGhost) (R : SepProp) (s0 s : State) (hr : DeserializeScopeP x.r)
    (hs : DeserLoopX C ctl x R s0 (recFieldsX x.r).length s) :
    DeserStepX C ctl x R s0 s (DeserRetX x R s0) abs := by
  let _ := hr
  rcases hs with ⟨hpc, hrun, ⟨htr, hvregs⟩, _hsym, _hfr, hsp, hal, hx29, hx19, hx20, _hx23, hmem⟩
  have hpc' : s.pc =
      (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr recDeserializeName + 0x254#64 := hpc
  let L := deserSpL s0.sp
  let v := ssgxAfter x.r (recFieldsX x.r).length
  let bs := encodeRecord x.r
  change s.mem ⊨ deserLocalsX L x.p bs
      (((recFieldsX x.r).drop (recFieldsX x.r).length).flatMap GenFieldX.enc) v ∗
    memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R at hmem
  rw [List.drop_length, List.flatMap_nil] at hmem
  unfold deserLocalsX at hmem
  rw [sliceCursorAfter_nil_dexit L x.p bs, memRegion_3f8_split_dexit L,
      deserSaved_eq_atL_dexit s0] at hmem
  let c0 := x.p + BitVec.ofNat 64 bs.length
  have hmem1 : s.mem ⊨
      prostSSGXAt A0 (L + 0x420#64) v ∗
      (memRegion x.out 368 ∗
       memRegion L 8 ∗
       (memRegion (L + 8#64) 336 ∗ memRegion (L + 0x158#64) 336 ∗
         memRegion (L + 0x2a8#64) 336) ∗
       ((L + 0x3f8#64) ↦₆₄ c0) ∗ ((L + 0x400#64) ↦₆₄ 0#64) ∗ (x.p ↦ₛ bs) ∗
       ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
       memRegion (L + 0x578#64) 0x170 ∗
       ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗ memRegion (L + 0x6f0#64) 0x20 ∗
       stackAt L deserCalleeStack ∗ deserSavedAtL_dexit L s0 ∗ R) := by
    dsimp only [c0]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
  obtain ⟨w0, rest, H, hw0, hrest, hrebuild, hmem2⟩ := satisfies_prostSSGXAt_move_dexit hmem1
  have hmem3 : s.mem ⊨
      memRegion x.out 368 ∗
      (((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗ H ∗
       memRegion L 8 ∗
       (memRegion (L + 8#64) 336 ∗ memRegion (L + 0x158#64) 336 ∗
         memRegion (L + 0x2a8#64) 336) ∗
       ((L + 0x3f8#64) ↦₆₄ c0) ∗ ((L + 0x400#64) ↦₆₄ 0#64) ∗ (x.p ↦ₛ bs) ∗
       ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
       memRegion (L + 0x578#64) 0x170 ∗
       ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗ memRegion (L + 0x6f0#64) 0x20 ∗
       stackAt L deserCalleeStack ∗ deserSavedAtL_dexit L s0 ∗ R) := by
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem2
  obtain ⟨u0, u1, u2, u3, hmem3'⟩ := satisfies_memRegion_out_split_dexit hmem3
  let F := (x.p ↦ₛ bs) ∗ H ∗ stackAt L deserCalleeStack ∗ memRegion L 8 ∗
    ((L + 0x3f8#64) ↦₆₄ c0) ∗ memRegion (L + 0x578#64) 0x170 ∗
    memRegion (L + 0x6f0#64) 0x20 ∗ R
  have hmem4 : s.mem ⊨
      (memRegion (L + 8#64) 336 ∗ memRegion (L + 0x158#64) 336 ∗ memRegion (L + 0x2a8#64) 336 ∗
        ((L + 0x400#64) ↦₆₄ 0#64) ∗
        ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
        ((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗
        ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
        (x.out ↦₆₄ u0) ∗ ((x.out + 8#64) ↦₆₄ u1) ∗
        ((x.out + 0x10#64) ↦₆₄ u2) ∗ ((x.out + 0x18#64) ↦₆₄ u3) ∗
        memRegion (x.out + 0x20#64) 336 ∗
        deserSavedAtL_dexit L s0) ∗ F := by
    dsimp only [F]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem3'
  intro hL
  have hwp := dexit_sepWP_dexit (abs := abs) (s0 := s0) (u0 := u0) (u1 := u1) (u2 := u2) (u3 := u3)
    hpc' hrun hsp hal hx29 hx19 hx20 hvregs hw0 hrest
  rcases hwp.elim hmem4 hL with
    ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, hspf, htracef, hcsf, rfl⟩ | ⟨_, hoom⟩⟩
  swap; · exact (not_satisfies_false_sepConj hoom).elim
  have hspf0 : sf.sp = s0.sp := by
    rw [hspf]
    dsimp [L, deserSpL]
    bv_omega
  refine ⟨sf, hsteps, Or.inl ⟨⟨hpcf, hspf0, hrunf⟩, ⟨hspf0, hcsf⟩, ?_⟩⟩
  have hmf1 : sf.mem ⊨
      ((x.p ↦ₛ bs) ∗
       ((x.out ↦₆₄ 0#64) ∗ ((x.out + 8#64) ↦₆₄ 8#64) ∗ ((x.out + 0x10#64) ↦₆₄ 0#64) ∗
         (((x.out + 0x18#64) ↦₆₄ w0) ∗ ((x.out + 0x20#64) ↦ₛ rest) ∗ H)) ∗
       (stackAt L deserCalleeStack ∗
        (memRegion L 8 ∗
          ((L + 8#64) ↦ₛ rest) ∗ ((L + 0x158#64) ↦ₛ rest) ∗ ((L + 0x2a8#64) ↦ₛ rest) ∗
          ((L + 0x3f8#64) ↦₆₄ c0) ∗ ((L + 0x400#64) ↦₆₄ 0#64) ∗
          ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
          ((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗
          memRegion (L + 0x578#64) 0x170 ∗
          ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
          memRegion (L + 0x6f0#64) 0x20 ∗
          deserSavedAtL_dexit L s0))) ∗ R := by
    dsimp only [F, L] at hmf ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmf
  have hout20 : x.out + 0x18#64 + 8#64 = x.out + 0x20#64 := by bv_omega
  have hss_out :
      ((x.out + 0x18#64) ↦₆₄ w0) ∗ ((x.out + 0x20#64) ↦ₛ rest) ∗ H ⊢
        prostSSGXAt A0 (x.out + 0x18#64) v := by
    have hr := hrebuild (x.out + 0x18#64)
    rwa [hout20] at hr
  have hstk := dexit_frame_entails_stackAt_dexit s0 c0 w0 rest hrest
  dsimp only at hstk
  have hmf2 := Satisfies.mono
    (sepConj_mono_left (sepConj_mono_right (sepConj_mono
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hss_out))) hstk))) hmf1
  unfold deserOutRawX deserOutRecordX
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htracef.trans htr, ?_⟩
  dsimp only [v, bs] at hmf2
  exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmf2

end CryptoVerification.E2E.Record.L1GX.Leaf.DeserDExitX
