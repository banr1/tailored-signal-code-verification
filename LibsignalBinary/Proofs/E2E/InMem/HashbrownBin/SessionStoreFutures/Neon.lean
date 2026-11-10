/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.E2E.InMem.HashbrownModel.FindInsert
import all Arm64.Trusted.ISA.Eval
import all Init.Data.Range.Basic
public import LibsignalBinary.Proofs.E2E.InMem.SipHashModel.Model
import ProofLib.BV.ReflectROBDD
import ProofLib.BV.WidthNorm

/-!
# NEON Probe-Group Lemmas for `InMemSessionStore`
-/

@[expose] public section

namespace CryptoVerification.E2E.InMem.HashbrownBin.SessionStoreFutures

open Arm64 ProofLib
open CryptoVerification.E2E.InMem.HashbrownModel
open CryptoVerification.E2E.InMem.SipHashModel

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

theorem dup8_lane (h : BitVec 64) :
    let v := (0#128 |||
      (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 |||
      (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 |||
      (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 |||
      (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 |||
      (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 |||
      (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 |||
      (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 |||
      (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56)
    (v >>> 0 &&& 255#128 = (h2Tag h).zeroExtend 128) ∧
    (v >>> 8 &&& 255#128 = (h2Tag h).zeroExtend 128) ∧
    (v >>> 16 &&& 255#128 = (h2Tag h).zeroExtend 128) ∧
    (v >>> 24 &&& 255#128 = (h2Tag h).zeroExtend 128) ∧
    (v >>> 32 &&& 255#128 = (h2Tag h).zeroExtend 128) ∧
    (v >>> 40 &&& 255#128 = (h2Tag h).zeroExtend 128) ∧
    (v >>> 48 &&& 255#128 = (h2Tag h).zeroExtend 128) ∧
    (v >>> 56 &&& 255#128 = (h2Tag h).zeroExtend 128) := by
  dsimp only [h2Tag]
  refine ⟨by bv_slice, by bv_slice, by bv_slice, by bv_slice,
          by bv_slice, by bv_slice, by bv_slice, by bv_slice⟩

theorem groupByte_lane (w : BitVec 64) :
    (BitVec.zeroExtend 128 w >>> 0 &&& 255#128 = (groupByte w 0).zeroExtend 128) ∧
    (BitVec.zeroExtend 128 w >>> 8 &&& 255#128 = (groupByte w 1).zeroExtend 128) ∧
    (BitVec.zeroExtend 128 w >>> 16 &&& 255#128 = (groupByte w 2).zeroExtend 128) ∧
    (BitVec.zeroExtend 128 w >>> 24 &&& 255#128 = (groupByte w 3).zeroExtend 128) ∧
    (BitVec.zeroExtend 128 w >>> 32 &&& 255#128 = (groupByte w 4).zeroExtend 128) ∧
    (BitVec.zeroExtend 128 w >>> 40 &&& 255#128 = (groupByte w 5).zeroExtend 128) ∧
    (BitVec.zeroExtend 128 w >>> 48 &&& 255#128 = (groupByte w 6).zeroExtend 128) ∧
    (BitVec.zeroExtend 128 w >>> 56 &&& 255#128 = (groupByte w 7).zeroExtend 128) := by
  dsimp only [groupByte]
  refine ⟨by bv_slice, by bv_slice, by bv_slice, by bv_slice,
          by bv_slice, by bv_slice, by bv_slice, by bv_slice⟩

theorem zeroExtend128_beq_8 (a b : BitVec 8) :
    (a.zeroExtend 128 == b.zeroExtend 128) = (a == b) := by
  by_cases hab : a = b
  · subst hab; simp
  · have hne : a.zeroExtend 128 ≠ b.zeroExtend 128 := by
      intro h; apply hab; bv_omega
    rw [beq_eq_false_iff_ne.mpr hne, beq_eq_false_iff_ne.mpr hab]

theorem truncate64_pack8_ite_and_mask (p0 p1 p2 p3 p4 p5 p6 p7 : Bool) :
    BitVec.truncate 64
      (0#128 |||
        ((if p0 = true then 255#128 else 0#128) &&& 255#128) <<< 0 |||
        ((if p1 = true then 255#128 else 0#128) &&& 255#128) <<< 8 |||
        ((if p2 = true then 255#128 else 0#128) &&& 255#128) <<< 16 |||
        ((if p3 = true then 255#128 else 0#128) &&& 255#128) <<< 24 |||
        ((if p4 = true then 255#128 else 0#128) &&& 255#128) <<< 32 |||
        ((if p5 = true then 255#128 else 0#128) &&& 255#128) <<< 40 |||
        ((if p6 = true then 255#128 else 0#128) &&& 255#128) <<< 48 |||
        ((if p7 = true then 255#128 else 0#128) &&& 255#128) <<< 56) &&&
      9259542123273814144#64 =
    packGroupWord
      (if p0 = true then 255#8 else 0#8)
      (if p1 = true then 255#8 else 0#8)
      (if p2 = true then 255#8 else 0#8)
      (if p3 = true then 255#8 else 0#8)
      (if p4 = true then 255#8 else 0#8)
      (if p5 = true then 255#8 else 0#8)
      (if p6 = true then 255#8 else 0#8)
      (if p7 = true then 255#8 else 0#8) &&&
      bitmaskIterMask := by
  cases p0 <;> cases p1 <;> cases p2 <;> cases p3 <;>
  cases p4 <;> cases p5 <;> cases p6 <;> cases p7 <;> rfl

theorem rawMatchTagMask_eq_findGroupIterMask (cbs : List (BitVec 8)) (pos : Nat) (h : BitVec 64) :
    BitVec.truncate 64
      (0#128 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> 0 &&& 255#128 ==
              (0#128 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56) >>> 0 &&& 255#128) = true
          then 255#128 else 0#128) &&& 255#128) <<< 0 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> 8 &&& 255#128 ==
              (0#128 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56) >>> 8 &&& 255#128) = true
          then 255#128 else 0#128) &&& 255#128) <<< 8 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> 16 &&& 255#128 ==
              (0#128 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56) >>> 16 &&& 255#128) = true
          then 255#128 else 0#128) &&& 255#128) <<< 16 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> 24 &&& 255#128 ==
              (0#128 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56) >>> 24 &&& 255#128) = true
          then 255#128 else 0#128) &&& 255#128) <<< 24 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> 32 &&& 255#128 ==
              (0#128 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56) >>> 32 &&& 255#128) = true
          then 255#128 else 0#128) &&& 255#128) <<< 32 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> 40 &&& 255#128 ==
              (0#128 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56) >>> 40 &&& 255#128) = true
          then 255#128 else 0#128) &&& 255#128) <<< 40 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> 48 &&& 255#128 ==
              (0#128 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56) >>> 48 &&& 255#128) = true
          then 255#128 else 0#128) &&& 255#128) <<< 48 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> 56 &&& 255#128 ==
              (0#128 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56) >>> 56 &&& 255#128) = true
          then 255#128 else 0#128) &&& 255#128) <<< 56) &&&
      9259542123273814144#64 =
    findGroupIterMask cbs pos (h2Tag h) := by
  obtain ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7⟩ := dup8_lane h
  obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7⟩ := groupByte_lane (loadGroupAt cbs pos)
  rw [hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7,
      hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7]
  simp only [zeroExtend128_beq_8]
  exact truncate64_pack8_ite_and_mask _ _ _ _ _ _ _ _

theorem ite_forInStep_yield {α : Type} (c : Prop) [Decidable c] (a b : α) :
    (if c then (pure (ForInStep.yield a) : Id (ForInStep α)) else pure (ForInStep.yield b)) =
    pure (ForInStep.yield (if c then a else b)) := by
  by_cases h : c <;> simp [h]

theorem forIn_range8_yield {α : Type} (init : α) (g : Nat → α → α) :
    Id.run (do
      let __s ← forIn [:8] init (fun i __s => pure (ForInStep.yield (g i __s)))
      pure __s) =
    (let c0 := g 0 init
     let c1 := g 1 c0
     let c2 := g 2 c1
     let c3 := g 3 c2
     let c4 := g 4 c3
     let c5 := g 5 c4
     let c6 := g 6 c5
     g 7 c6) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  rfl

theorem evalUmaxv8_unfold (vn : BitVec 128) :
    Id.run (do
      let __s ←
        forIn [:8] 0#128 fun i __s =>
          if BitVec.ult __s ((vn >>> (i * 8)) &&& 255#128) = true then
            pure (ForInStep.yield ((vn >>> (i * 8)) &&& 255#128))
          else pure (ForInStep.yield __s)
      pure __s) =
    (let c0 := if BitVec.ult 0#128 ((vn >>> 0) &&& 255#128) = true then (vn >>> 0) &&& 255#128 else 0#128
     let c1 := if BitVec.ult c0 ((vn >>> 8) &&& 255#128) = true then (vn >>> 8) &&& 255#128 else c0
     let c2 := if BitVec.ult c1 ((vn >>> 16) &&& 255#128) = true then (vn >>> 16) &&& 255#128 else c1
     let c3 := if BitVec.ult c2 ((vn >>> 24) &&& 255#128) = true then (vn >>> 24) &&& 255#128 else c2
     let c4 := if BitVec.ult c3 ((vn >>> 32) &&& 255#128) = true then (vn >>> 32) &&& 255#128 else c3
     let c5 := if BitVec.ult c4 ((vn >>> 40) &&& 255#128) = true then (vn >>> 40) &&& 255#128 else c4
     let c6 := if BitVec.ult c5 ((vn >>> 48) &&& 255#128) = true then (vn >>> 48) &&& 255#128 else c5
     if BitVec.ult c6 ((vn >>> 56) &&& 255#128) = true then (vn >>> 56) &&& 255#128 else c6) := by
  simp only [ite_forInStep_yield]
  exact forIn_range8_yield 0#128 (fun i __s =>
    if BitVec.ult __s ((vn >>> (i * 8)) &&& 255#128) = true then
      (vn >>> (i * 8)) &&& 255#128
    else __s)

theorem packGroupWord_lanes (x0 x1 x2 x3 x4 x5 x6 x7 : BitVec 8) :
    (BitVec.zeroExtend 128 (packGroupWord x0 x1 x2 x3 x4 x5 x6 x7) >>> 0 &&& 255#128 = x0.zeroExtend 128) ∧
    (BitVec.zeroExtend 128 (packGroupWord x0 x1 x2 x3 x4 x5 x6 x7) >>> 8 &&& 255#128 = x1.zeroExtend 128) ∧
    (BitVec.zeroExtend 128 (packGroupWord x0 x1 x2 x3 x4 x5 x6 x7) >>> 16 &&& 255#128 = x2.zeroExtend 128) ∧
    (BitVec.zeroExtend 128 (packGroupWord x0 x1 x2 x3 x4 x5 x6 x7) >>> 24 &&& 255#128 = x3.zeroExtend 128) ∧
    (BitVec.zeroExtend 128 (packGroupWord x0 x1 x2 x3 x4 x5 x6 x7) >>> 32 &&& 255#128 = x4.zeroExtend 128) ∧
    (BitVec.zeroExtend 128 (packGroupWord x0 x1 x2 x3 x4 x5 x6 x7) >>> 40 &&& 255#128 = x5.zeroExtend 128) ∧
    (BitVec.zeroExtend 128 (packGroupWord x0 x1 x2 x3 x4 x5 x6 x7) >>> 48 &&& 255#128 = x6.zeroExtend 128) ∧
    (BitVec.zeroExtend 128 (packGroupWord x0 x1 x2 x3 x4 x5 x6 x7) >>> 56 &&& 255#128 = x7.zeroExtend 128) := by
  dsimp only [packGroupWord]
  refine ⟨by bv_slice, by bv_slice, by bv_slice, by bv_slice,
          by bv_slice, by bv_slice, by bv_slice, by bv_slice⟩

theorem evalUmaxv_matchEmpty_mkCtrl4_raw (b0 b1 b2 b3 : BitVec 8) (pos : Nat) (hpos : pos < 4) :
    (Id.run do
      let __s ←
        forIn [:8] 0#128 fun i __s =>
          if
            BitVec.ult __s
              (((0#128 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 0 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 0 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 8 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 8 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 16 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 16 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 24 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 24 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 32 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 32 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 40 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 40 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 48 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 48 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 56 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 56) >>> (i * 8)) &&& 255#128) = true
          then
            pure (ForInStep.yield
              (((0#128 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 0 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 0 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 8 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 8 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 16 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 16 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 24 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 24 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 32 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 32 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 40 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 40 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 48 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 48 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 56 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 56) >>> (i * 8)) &&& 255#128))
          else pure (ForInStep.yield __s)
      pure __s) = 255#128 := by
  rcases (by omega : pos = 0 ∨ pos = 1 ∨ pos = 2 ∨ pos = 3) with rfl | rfl | rfl | rfl
  · obtain ⟨hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7⟩ :=
      packGroupWord_lanes b0 b1 b2 b3 emptyTag emptyTag emptyTag emptyTag
    rw [loadGroupAt_mkCtrl4_0, hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7]
    dsimp only [emptyTag]
    by_cases h0 : b0.zeroExtend 128 = 255#128 <;>
    by_cases h1 : b1.zeroExtend 128 = 255#128 <;>
    by_cases h2 : b2.zeroExtend 128 = 255#128 <;>
    by_cases h3 : b3.zeroExtend 128 = 255#128 <;>
    simp only [h0, h1, h2, h3, ↓reduceIte] <;>
    (rw [evalUmaxv8_unfold]; rfl)
  · obtain ⟨hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7⟩ :=
      packGroupWord_lanes b1 b2 b3 emptyTag emptyTag emptyTag emptyTag b0
    rw [loadGroupAt_mkCtrl4_1, hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7]
    dsimp only [emptyTag]
    by_cases h0 : b0.zeroExtend 128 = 255#128 <;>
    by_cases h1 : b1.zeroExtend 128 = 255#128 <;>
    by_cases h2 : b2.zeroExtend 128 = 255#128 <;>
    by_cases h3 : b3.zeroExtend 128 = 255#128 <;>
    simp only [h0, h1, h2, h3, ↓reduceIte] <;>
    (rw [evalUmaxv8_unfold]; rfl)
  · obtain ⟨hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7⟩ :=
      packGroupWord_lanes b2 b3 emptyTag emptyTag emptyTag emptyTag b0 b1
    rw [loadGroupAt_mkCtrl4_2, hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7]
    dsimp only [emptyTag]
    by_cases h0 : b0.zeroExtend 128 = 255#128 <;>
    by_cases h1 : b1.zeroExtend 128 = 255#128 <;>
    by_cases h2 : b2.zeroExtend 128 = 255#128 <;>
    by_cases h3 : b3.zeroExtend 128 = 255#128 <;>
    simp only [h0, h1, h2, h3, ↓reduceIte] <;>
    (rw [evalUmaxv8_unfold]; rfl)
  · obtain ⟨hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7⟩ :=
      packGroupWord_lanes b3 emptyTag emptyTag emptyTag emptyTag b0 b1 b2
    rw [loadGroupAt_mkCtrl4_3, hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7]
    dsimp only [emptyTag]
    by_cases h0 : b0.zeroExtend 128 = 255#128 <;>
    by_cases h1 : b1.zeroExtend 128 = 255#128 <;>
    by_cases h2 : b2.zeroExtend 128 = 255#128 <;>
    by_cases h3 : b3.zeroExtend 128 = 255#128 <;>
    simp only [h0, h1, h2, h3, ↓reduceIte] <;>
    (rw [evalUmaxv8_unfold]; rfl)

theorem evalUmaxv_matchEmpty_mkCtrl4_getLsbD_zero
    (b0 b1 b2 b3 : BitVec 8) (pos : Nat) (hpos : pos < 4) :
    (BitVec.zeroExtend 64
      (BitVec.truncate 32
        (Id.run do
          let __s ←
            forIn [:8] 0#128 fun i __s =>
              if
                BitVec.ult __s
                  (((0#128 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 0 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 0 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 8 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 8 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 16 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 16 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 24 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 24 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 32 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 32 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 40 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 40 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 48 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 48 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 56 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 56) >>> (i * 8)) &&& 255#128) = true
              then
                pure (ForInStep.yield
                  (((0#128 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 0 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 0 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 8 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 8 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 16 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 16 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 24 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 24 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 32 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 32 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 40 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 40 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 48 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 48 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 56 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 56) >>> (i * 8)) &&& 255#128))
              else pure (ForInStep.yield __s)
          pure __s))).getLsbD (OfNat.ofNat 0) = true := by
  rw [evalUmaxv_matchEmpty_mkCtrl4_raw b0 b1 b2 b3 pos hpos]
  decide

theorem eval_probeBucket_singleCtrl4 (k pos : Nat) (hk : k < 4) (hpos : pos < 4) :
    (BitVec.ofNat 64 pos +
      ((BitVec.ofNat 64 (countLeadingZeros (reverseBits (laneBit (laneOfBucket4 pos k))))) >>> 3)) &&&
      3#64 = BitVec.ofNat 64 k := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
  rcases (by omega : pos = 0 ∨ pos = 1 ∨ pos = 2 ∨ pos = 3) with rfl | rfl | rfl | rfl <;>
  decide +kernel

theorem eval_probeBucket_singleCtrl4' (k pos : Nat) (hk : k < 4) (hpos : pos < 4) :
    (BitVec.ofNat 64 pos +
      (laneBit (laneOfBucket4 pos k)).reverse.clz >>> 3 &&&
      3#64) = BitVec.ofNat 64 k := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
  rcases (by omega : pos = 0 ∨ pos = 1 ∨ pos = 2 ∨ pos = 3) with rfl | rfl | rfl | rfl <;>
  decide +kernel

theorem eval_clearLowestBit_laneBit (k pos : Nat) (hk : k < 4) (hpos : pos < 4) :
    laneBit (laneOfBucket4 pos k) &&& (laneBit (laneOfBucket4 pos k) + bv% (2 ^ 64 - 1)) = 0#64 := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
  rcases (by omega : pos = 0 ∨ pos = 1 ∨ pos = 2 ∨ pos = 3) with rfl | rfl | rfl | rfl <;>
  decide +kernel

theorem eval_clearLowestBit_laneBit' (k pos : Nat) (hk : k < 4) (hpos : pos < 4) :
    (laneBit (laneOfBucket4 pos k) + bv% (2 ^ 64 - 1)) &&& laneBit (laneOfBucket4 pos k) = 0#64 := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
  rcases (by omega : pos = 0 ∨ pos = 1 ∨ pos = 2 ∨ pos = 3) with rfl | rfl | rfl | rfl <;>
  decide +kernel

theorem eval_clearLowestBit_laneBit_sub (k pos : Nat) (hk : k < 4) (hpos : pos < 4) :
    (laneBit (laneOfBucket4 pos k) - 1#64 &&& laneBit (laneOfBucket4 pos k)) = 0#64 := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
  rcases (by omega : pos = 0 ∨ pos = 1 ∨ pos = 2 ∨ pos = 3) with rfl | rfl | rfl | rfl <;>
  decide +kernel

theorem laneBit_laneOfBucket4_ne_zero (k pos : Nat) (hk : k < 4) (hpos : pos < 4) :
    laneBit (laneOfBucket4 pos k) ≠ 0#64 := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
  rcases (by omega : pos = 0 ∨ pos = 1 ∨ pos = 2 ∨ pos = 3) with rfl | rfl | rfl | rfl <;>
  decide +kernel

theorem findGroupIterMask_singleCtrl4_eq_zero_imp_ne
    (k0 k1 : BitVec 64) (k : Nat) (hk : k < 4)
    (peerName qName : List (BitVec 8)) (peerDev qDev : BitVec 8)
    (hmask0 :
      findGroupIterMask (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev)))
        (hashAddrBv k0 k1 qName qDev &&& 3#64).toNat
        (h2Tag (hashAddrBv k0 k1 qName qDev)) = 0#64) :
    ¬(qName = peerName ∧ qDev = peerDev) := by
  rintro ⟨rfl, rfl⟩
  have hpos : (hashAddrBv k0 k1 qName qDev &&& 3#64).toNat < 4 :=
    probePos_3_toNat_lt (hashAddrBv k0 k1 qName qDev)
  rw [findGroupIterMask_singleCtrl4 k _ hk hpos] at hmask0
  simp only [beq_self_eq_true, ↓reduceIte] at hmask0
  exact laneBit_laneOfBucket4_ne_zero k _ hk hpos hmask0

theorem findGroupIterMask_singleCtrl4_ne_zero_eq
    (k0 k1 : BitVec 64) (k pos : Nat) (hk : k < 4) (hpos : pos < 4)
    (peerName qName : List (BitVec 8)) (peerDev qDev : BitVec 8)
    (hmask_ne :
      ¬findGroupIterMask (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev)))
        pos (h2Tag (hashAddrBv k0 k1 qName qDev)) = 0#64) :
    findGroupIterMask (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev)))
      pos (h2Tag (hashAddrBv k0 k1 qName qDev)) =
      laneBit (laneOfBucket4 pos k) := by
  rw [findGroupIterMask_singleCtrl4 k pos hk hpos] at hmask_ne ⊢
  split
  · rfl
  · rename_i hne
    exfalso
    exact hmask_ne (by simp [hne])

theorem findGroupIterMask_singleCtrl4_ne_zero_tag_eq
    (k0 k1 : BitVec 64) (k pos : Nat) (hk : k < 4) (hpos : pos < 4)
    (peerName qName : List (BitVec 8)) (peerDev qDev : BitVec 8)
    (hmask_ne :
      ¬findGroupIterMask (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev)))
        pos (h2Tag (hashAddrBv k0 k1 qName qDev)) = 0#64) :
    h2Tag (hashAddrBv k0 k1 peerName peerDev) = h2Tag (hashAddrBv k0 k1 qName qDev) := by
  rw [findGroupIterMask_singleCtrl4 k pos hk hpos] at hmask_ne
  split at hmask_ne
  · rename_i heq
    exact eq_of_beq heq
  · exfalso
    exact hmask_ne rfl

end CryptoVerification.E2E.InMem.HashbrownBin.SessionStoreFutures
