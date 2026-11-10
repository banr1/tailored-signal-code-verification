/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeVarintBase
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeVarintDecodes
import ProofLib.SepLogic.WPp

/-!
# Multi-Byte Stages and No-Grow Contract for `encode_varint`

Continuation stages 4–9 and top-level proof `encodeVarintNoGrow_ok` for
`prost::encoding::varint::encode_varint::<Vec<u8>>` (`0x30a0`) when spare capacity suffices.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncode

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
open EncodeVarintNorm

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem step_encVarint_s4_trap (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (val v curCap curPtr : BitVec 64) (curBs : List (BitVec 8))
    (hlt : curBs.length < curCap.toNat)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName + 360#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length)
    (hx9 : s.readReg64 .x9 = curCap)
    (hx12 : s.readReg64 .x12 = val >>> 28)
    (hcs : EncVarintCalleeSaved s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if (val >>> 28).ult 128#64 then
        (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName + 512#64
      else
        (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName + 476#64) →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = (if (val >>> 28).ult 128#64 then val >>> 28 else val) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 21)]).length →
      sm.readReg64 .x9 = curCap →
      sm.readReg64 .x10 = curPtr →
      sm.readReg64 .x11 = val >>> 35 →
      sm.readReg64 .x12 = val >>> 28 →
      EncVarintCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 21)]).length) ∗
          vecU8Buf A curCap curPtr (curBs ++ [varintContByte (val >>> 21)])) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q Qp := by
  have hf360 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 360)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3208
  have hf364 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 364)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x320c
  have hf368 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 368)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3210
  have hf372 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 372)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3214
  have hf376 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 376)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3218
  have hf380 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 380)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x321c
  have hf384 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 384)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3220
  have hf388 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 388)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3224
  have hf392 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 392)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3228
  have hf396 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 396)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x322c
  have hf400 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 400)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3230
  have hf404 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 404)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3234
  revert hpc hnext hf360 hf364 hf368 hf372 hf376 hf380 hf384 hf388 hf392 hf396 hf400 hf404
  generalize (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName = entry
  intro hpc hnext hf360 hf364 hf368 hf372 hf376 hf380 hf384 hf388 hf392 hf396 hf400 hf404
  examples_hide_fetches
  subst hP
  rcases hcs with ⟨h21, h22, h23, h24, h25, h26, h27, h28, hvregs⟩
  have hbeq := cap_beq_len_false hlt
  have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 21))
  rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  cases hbr : (val >>> 28).ult 128#64
  · apply SepWPp.of_sepWP (mid := entry + 476#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 21)) hlt]
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [EncVarintCalleeSaved, arm64_norm, *])
  · apply SepWPp.of_sepWP (mid := entry + 512#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 21)) hlt]
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [EncVarintCalleeSaved, arm64_norm, *])

theorem step_encVarint_s4 (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (val v curCap curPtr : BitVec 64) (curBs : List (BitVec 8))
    (hlt : curBs.length < curCap.toNat)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeVarintName + 360#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length)
    (hx9 : s.readReg64 .x9 = curCap)
    (hx12 : s.readReg64 .x12 = val >>> 28)
    (hcs : EncVarintCalleeSaved s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if (val >>> 28).ult 128#64 then
        (tripleRatchetProgAt b C ctl abs).fnAddr encodeVarintName + 512#64
      else
        (tripleRatchetProgAt b C ctl abs).fnAddr encodeVarintName + 476#64) →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = (if (val >>> 28).ult 128#64 then val >>> 28 else val) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 21)]).length →
      sm.readReg64 .x9 = curCap →
      sm.readReg64 .x10 = curPtr →
      sm.readReg64 .x11 = val >>> 35 →
      sm.readReg64 .x12 = val >>> 28 →
      EncVarintCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 21)]).length) ∗
          vecU8Buf A curCap curPtr (curBs ++ [varintContByte (val >>> 21)])) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q Qp :=
  step_encVarint_s4_trap b A (tripleRatchetExterns C ctl abs) val v curCap curPtr curBs hlt hpc hrun hx0 hx1 hx8 hx9 hx12 hcs hP hnext
theorem step_encVarint_s5_trap (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (val v curCap curPtr : BitVec 64) (curBs : List (BitVec 8))
    (hlt : curBs.length < curCap.toNat)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName + 476#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length)
    (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = curPtr)
    (hx11 : s.readReg64 .x11 = val >>> 35)
    (hx12 : s.readReg64 .x12 = val >>> 28)
    (hcs : EncVarintCalleeSaved s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if (val >>> 35).ult 128#64 then
        (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName + 512#64
      else
        (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName + 668#64) →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = (if (val >>> 35).ult 128#64 then val >>> 35 else val) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 28)]).length →
      sm.readReg64 .x9 = curCap →
      sm.readReg64 .x10 = curPtr →
      sm.readReg64 .x11 = val >>> 35 →
      sm.readReg64 .x12 = val >>> 42 →
      EncVarintCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 28)]).length) ∗
          vecU8Buf A curCap curPtr (curBs ++ [varintContByte (val >>> 28)])) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q Qp := by
  have hf476 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 476)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x327c
  have hf480 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 480)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3280
  have hf484 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 484)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3284
  have hf488 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 488)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3288
  have hf492 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 492)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x328c
  have hf496 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 496)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3290
  have hf500 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 500)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3294
  have hf504 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 504)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3298
  have hf508 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 508)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x329c
  revert hpc hnext hf476 hf480 hf484 hf488 hf492 hf496 hf500 hf504 hf508
  generalize (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName = entry
  intro hpc hnext hf476 hf480 hf484 hf488 hf492 hf496 hf500 hf504 hf508
  examples_hide_fetches
  subst hP
  rcases hcs with ⟨h21, h22, h23, h24, h25, h26, h27, h28, hvregs⟩
  have hbeq := cap_beq_len_false hlt
  have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 28))
  rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  cases hbr : (val >>> 35).ult 128#64
  · apply SepWPp.of_sepWP (mid := entry + 668#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 28)) hlt]
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [EncVarintCalleeSaved, arm64_norm, *])
  · apply SepWPp.of_sepWP (mid := entry + 512#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 28)) hlt]
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [EncVarintCalleeSaved, arm64_norm, *])

theorem step_encVarint_s5 (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (val v curCap curPtr : BitVec 64) (curBs : List (BitVec 8))
    (hlt : curBs.length < curCap.toNat)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeVarintName + 476#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length)
    (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = curPtr)
    (hx11 : s.readReg64 .x11 = val >>> 35)
    (hx12 : s.readReg64 .x12 = val >>> 28)
    (hcs : EncVarintCalleeSaved s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if (val >>> 35).ult 128#64 then
        (tripleRatchetProgAt b C ctl abs).fnAddr encodeVarintName + 512#64
      else
        (tripleRatchetProgAt b C ctl abs).fnAddr encodeVarintName + 668#64) →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = (if (val >>> 35).ult 128#64 then val >>> 35 else val) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 28)]).length →
      sm.readReg64 .x9 = curCap →
      sm.readReg64 .x10 = curPtr →
      sm.readReg64 .x11 = val >>> 35 →
      sm.readReg64 .x12 = val >>> 42 →
      EncVarintCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 28)]).length) ∗
          vecU8Buf A curCap curPtr (curBs ++ [varintContByte (val >>> 28)])) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q Qp :=
  step_encVarint_s5_trap b A (tripleRatchetExterns C ctl abs) val v curCap curPtr curBs hlt hpc hrun hx0 hx1 hx8 hx9 hx10 hx11 hx12 hcs hP hnext
theorem step_encVarint_s6_trap (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (val v curCap curPtr : BitVec 64) (curBs : List (BitVec 8))
    (hlt : curBs.length < curCap.toNat)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName + 668#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length)
    (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = curPtr)
    (hx11 : s.readReg64 .x11 = val >>> 35)
    (hx12 : s.readReg64 .x12 = val >>> 42)
    (hcs : EncVarintCalleeSaved s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if (val >>> 42).ult 128#64 then
        (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName + 512#64
      else
        (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName + 704#64) →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = (if (val >>> 42).ult 128#64 then val >>> 42 else val) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 35)]).length →
      sm.readReg64 .x9 = curCap →
      sm.readReg64 .x11 = val >>> 49 →
      sm.readReg64 .x12 = val >>> 42 →
      EncVarintCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 35)]).length) ∗
          vecU8Buf A curCap curPtr (curBs ++ [varintContByte (val >>> 35)])) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q Qp := by
  have hf668 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 668)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x333c
  have hf672 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 672)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3340
  have hf676 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 676)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3344
  have hf680 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 680)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3348
  have hf684 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 684)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x334c
  have hf688 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 688)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3350
  have hf692 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 692)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3354
  have hf696 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 696)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3358
  have hf700 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 700)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x335c
  have hf400 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 400)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3230
  have hf404 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 404)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3234
  revert hpc hnext hf668 hf672 hf676 hf680 hf684 hf688 hf692 hf696 hf700 hf400 hf404
  generalize (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName = entry
  intro hpc hnext hf668 hf672 hf676 hf680 hf684 hf688 hf692 hf696 hf700 hf400 hf404
  examples_hide_fetches
  subst hP
  rcases hcs with ⟨h21, h22, h23, h24, h25, h26, h27, h28, hvregs⟩
  have hbeq := cap_beq_len_false hlt
  have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 35))
  rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  cases hbr : (val >>> 42).ult 128#64
  · apply SepWPp.of_sepWP (mid := entry + 704#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 35)) hlt]
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [EncVarintCalleeSaved, arm64_norm, *])
  · apply SepWPp.of_sepWP (mid := entry + 512#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 35)) hlt]
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [EncVarintCalleeSaved, arm64_norm, *])

theorem step_encVarint_s6 (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (val v curCap curPtr : BitVec 64) (curBs : List (BitVec 8))
    (hlt : curBs.length < curCap.toNat)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeVarintName + 668#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length)
    (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = curPtr)
    (hx11 : s.readReg64 .x11 = val >>> 35)
    (hx12 : s.readReg64 .x12 = val >>> 42)
    (hcs : EncVarintCalleeSaved s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if (val >>> 42).ult 128#64 then
        (tripleRatchetProgAt b C ctl abs).fnAddr encodeVarintName + 512#64
      else
        (tripleRatchetProgAt b C ctl abs).fnAddr encodeVarintName + 704#64) →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = (if (val >>> 42).ult 128#64 then val >>> 42 else val) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 35)]).length →
      sm.readReg64 .x9 = curCap →
      sm.readReg64 .x11 = val >>> 49 →
      sm.readReg64 .x12 = val >>> 42 →
      EncVarintCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 35)]).length) ∗
          vecU8Buf A curCap curPtr (curBs ++ [varintContByte (val >>> 35)])) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q Qp :=
  step_encVarint_s6_trap b A (tripleRatchetExterns C ctl abs) val v curCap curPtr curBs hlt hpc hrun hx0 hx1 hx8 hx9 hx10 hx11 hx12 hcs hP hnext
theorem step_encVarint_s7_trap (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (val v curCap curPtr : BitVec 64) (curBs : List (BitVec 8))
    (hlt : curBs.length < curCap.toNat)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName + 704#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length)
    (hx9 : s.readReg64 .x9 = curCap)
    (hx11 : s.readReg64 .x11 = val >>> 49)
    (hx12 : s.readReg64 .x12 = val >>> 42)
    (hcs : EncVarintCalleeSaved s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if (val >>> 49).ult 128#64 then
        (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName + 512#64
      else
        (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName + 740#64) →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = (if (val >>> 49).ult 128#64 then val >>> 49 else val) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 42)]).length →
      sm.readReg64 .x9 = curCap →
      sm.readReg64 .x10 = val >>> 56 →
      sm.readReg64 .x11 = val >>> 49 →
      sm.readReg64 .x12 = curPtr →
      EncVarintCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 42)]).length) ∗
          vecU8Buf A curCap curPtr (curBs ++ [varintContByte (val >>> 42)])) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q Qp := by
  have hf704 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 704)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3360
  have hf708 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 708)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3364
  have hf712 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 712)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3368
  have hf716 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 716)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x336c
  have hf720 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 720)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3370
  have hf724 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 724)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3374
  have hf728 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 728)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3378
  have hf732 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 732)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x337c
  have hf736 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 736)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3380
  have hf508 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 508)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x329c
  revert hpc hnext hf704 hf708 hf712 hf716 hf720 hf724 hf728 hf732 hf736 hf508
  generalize (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName = entry
  intro hpc hnext hf704 hf708 hf712 hf716 hf720 hf724 hf728 hf732 hf736 hf508
  examples_hide_fetches
  subst hP
  rcases hcs with ⟨h21, h22, h23, h24, h25, h26, h27, h28, hvregs⟩
  have hbeq := cap_beq_len_false hlt
  have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 42))
  rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  cases hbr : (val >>> 49).ult 128#64
  · apply SepWPp.of_sepWP (mid := entry + 740#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 42)) hlt]
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [EncVarintCalleeSaved, arm64_norm, *])
  · apply SepWPp.of_sepWP (mid := entry + 512#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 42)) hlt]
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [EncVarintCalleeSaved, arm64_norm, *])

theorem step_encVarint_s7 (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (val v curCap curPtr : BitVec 64) (curBs : List (BitVec 8))
    (hlt : curBs.length < curCap.toNat)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeVarintName + 704#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length)
    (hx9 : s.readReg64 .x9 = curCap)
    (hx11 : s.readReg64 .x11 = val >>> 49)
    (hx12 : s.readReg64 .x12 = val >>> 42)
    (hcs : EncVarintCalleeSaved s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if (val >>> 49).ult 128#64 then
        (tripleRatchetProgAt b C ctl abs).fnAddr encodeVarintName + 512#64
      else
        (tripleRatchetProgAt b C ctl abs).fnAddr encodeVarintName + 740#64) →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = (if (val >>> 49).ult 128#64 then val >>> 49 else val) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 42)]).length →
      sm.readReg64 .x9 = curCap →
      sm.readReg64 .x10 = val >>> 56 →
      sm.readReg64 .x11 = val >>> 49 →
      sm.readReg64 .x12 = curPtr →
      EncVarintCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 42)]).length) ∗
          vecU8Buf A curCap curPtr (curBs ++ [varintContByte (val >>> 42)])) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q Qp :=
  step_encVarint_s7_trap b A (tripleRatchetExterns C ctl abs) val v curCap curPtr curBs hlt hpc hrun hx0 hx1 hx8 hx9 hx11 hx12 hcs hP hnext
theorem step_encVarint_s8_trap (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (val v curCap curPtr : BitVec 64) (curBs : List (BitVec 8))
    (hlt : curBs.length < curCap.toNat)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName + 740#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length)
    (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = val >>> 56)
    (hx11 : s.readReg64 .x11 = val >>> 49)
    (hx12 : s.readReg64 .x12 = curPtr)
    (hcs : EncVarintCalleeSaved s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if (val >>> 56).ult 128#64 then
        (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName + 512#64
      else
        (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName + 984#64) →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = (if (val >>> 56).ult 128#64 then val >>> 56 else val) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 49)]).length →
      sm.readReg64 .x9 = curCap →
      sm.readReg64 .x10 = val >>> 56 →
      sm.readReg64 .x12 = curPtr →
      EncVarintCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 49)]).length) ∗
          vecU8Buf A curCap curPtr (curBs ++ [varintContByte (val >>> 49)])) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q Qp := by
  have hf740 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 740)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3384
  have hf744 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 744)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3388
  have hf748 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 748)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x338c
  have hf752 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 752)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3390
  have hf756 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 756)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3394
  have hf760 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 760)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3398
  have hf764 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 764)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x339c
  have hf768 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 768)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x33a0
  have hf772 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 772)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x33a4
  revert hpc hnext hf740 hf744 hf748 hf752 hf756 hf760 hf764 hf768 hf772
  generalize (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName = entry
  intro hpc hnext hf740 hf744 hf748 hf752 hf756 hf760 hf764 hf768 hf772
  examples_hide_fetches
  subst hP
  rcases hcs with ⟨h21, h22, h23, h24, h25, h26, h27, h28, hvregs⟩
  have hbeq := cap_beq_len_false hlt
  have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 49))
  rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  cases hbr : (val >>> 56).ult 128#64
  · apply SepWPp.of_sepWP (mid := entry + 984#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 49)) hlt]
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [EncVarintCalleeSaved, arm64_norm, *])
  · apply SepWPp.of_sepWP (mid := entry + 512#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 49)) hlt]
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [EncVarintCalleeSaved, arm64_norm, *])

theorem step_encVarint_s8 (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (val v curCap curPtr : BitVec 64) (curBs : List (BitVec 8))
    (hlt : curBs.length < curCap.toNat)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeVarintName + 740#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length)
    (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = val >>> 56)
    (hx11 : s.readReg64 .x11 = val >>> 49)
    (hx12 : s.readReg64 .x12 = curPtr)
    (hcs : EncVarintCalleeSaved s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if (val >>> 56).ult 128#64 then
        (tripleRatchetProgAt b C ctl abs).fnAddr encodeVarintName + 512#64
      else
        (tripleRatchetProgAt b C ctl abs).fnAddr encodeVarintName + 984#64) →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = (if (val >>> 56).ult 128#64 then val >>> 56 else val) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 49)]).length →
      sm.readReg64 .x9 = curCap →
      sm.readReg64 .x10 = val >>> 56 →
      sm.readReg64 .x12 = curPtr →
      EncVarintCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 49)]).length) ∗
          vecU8Buf A curCap curPtr (curBs ++ [varintContByte (val >>> 49)])) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q Qp :=
  step_encVarint_s8_trap b A (tripleRatchetExterns C ctl abs) val v curCap curPtr curBs hlt hpc hrun hx0 hx1 hx8 hx9 hx10 hx11 hx12 hcs hP hnext
theorem step_encVarint_s9_trap (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (val v curCap curPtr : BitVec 64) (curBs : List (BitVec 8))
    (hlt : curBs.length < curCap.toNat)
    (hbit : (val >>> 56).ult 128#64 = false)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName + 984#64)
    (hrun : s.status = .Running)
    (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length)
    (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = val >>> 56)
    (hx12 : s.readReg64 .x12 = curPtr)
    (hcs : EncVarintCalleeSaved s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName + 512#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = val >>> 63 →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 56)]).length →
      sm.readReg64 .x9 = curCap →
      EncVarintCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 56)]).length) ∗
          vecU8Buf A curCap curPtr (curBs ++ [varintContByte (val >>> 56)])) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q Qp := by
  have hf984 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 984)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3478
  have hf988 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 988)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x347c
  have hf992 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 992)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3480
  have hf996 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 996)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3484
  have hf1000 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 1000)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3488
  have hf1004 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 1004)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x348c
  have hf1008 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 1008)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3490
  have hf1012 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 1012)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3494
  revert hpc hnext hf984 hf988 hf992 hf996 hf1000 hf1004 hf1008 hf1012
  generalize (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName = entry
  intro hpc hnext hf984 hf988 hf992 hf996 hf1000 hf1004 hf1008 hf1012
  examples_hide_fetches
  subst hP
  rcases hcs with ⟨h21, h22, h23, h24, h25, h26, h27, h28, hvregs⟩
  have hbeq := cap_beq_len_false hlt
  have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 56))
  rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP (mid := entry + 512#64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  rw [contByte9_contByte_eq val hbit, vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 56)) hlt]
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [contByte9_shr63_eq val hbit, arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [EncVarintCalleeSaved, arm64_norm, *])

theorem step_encVarint_s9 (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (val v curCap curPtr : BitVec 64) (curBs : List (BitVec 8))
    (hlt : curBs.length < curCap.toNat)
    (hbit : (val >>> 56).ult 128#64 = false)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeVarintName + 984#64)
    (hrun : s.status = .Running)
    (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length)
    (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = val >>> 56)
    (hx12 : s.readReg64 .x12 = curPtr)
    (hcs : EncVarintCalleeSaved s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeVarintName + 512#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = val >>> 63 →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 56)]).length →
      sm.readReg64 .x9 = curCap →
      EncVarintCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 56)]).length) ∗
          vecU8Buf A curCap curPtr (curBs ++ [varintContByte (val >>> 56)])) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q Qp :=
  step_encVarint_s9_trap b A (tripleRatchetExterns C ctl abs) val v curCap curPtr curBs hlt hbit hpc hrun hx1 hx8 hx9 hx10 hx12 hcs hP hnext

/-! ## No-Grow Specification and Proof -/

theorem encodeVarint_inv_done {k : Nat} {v : BitVec 64} {curBs bs : List (BitVec 8)} {val : BitVec 64}
    (h : v.ult 128#64 = true)
    (hinv : curBs ++ encodeVarintAux (k + 1) v = bs ++ encodeVarint val) :
    curBs ++ [v.setWidth 8] = bs ++ encodeVarint val := by
  rw [← hinv, encodeVarintAux_of_ult h]

theorem encodeVarint_inv_next {k : Nat} {v : BitVec 64} {curBs bs : List (BitVec 8)} {val : BitVec 64}
    (h : v.ult 128#64 = false)
    (hinv : curBs ++ encodeVarintAux (k + 1) v = bs ++ encodeVarint val) :
    (curBs ++ [varintContByte v]) ++ encodeVarintAux k (v >>> 7) = bs ++ encodeVarint val := by
  rw [List.append_assoc, List.singleton_append, ← encodeVarintAux_of_not_ult h, hinv]

theorem step_encVarint_noGrow_trap (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (val v cap ptr sp v48 v40 v32 v24 v16 v8 : BitVec 64) (bs : List (BitVec 8))
    (hle : bs.length + (encodeVarint val).length ≤ cap.toNat)
    {s0 : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s0.readReg64 .x0 = val)
    (hx1 : s0.readReg64 .x1 = v)
    (hP : P = ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Buf A cap ptr bs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      ((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
      ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8) ∗
      A.pool ∗ stackAt (sp - 48#64) doReserveStack) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf →
      Q sf (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bs ++ encodeVarint val).length) ∗
        vecU8Buf A cap ptr (bs ++ encodeVarint val) ∗
        ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
        ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
        A.pool ∗ stackAt (sp - 48#64) doReserveStack) ∗ F)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s0 P Q Qp := by
  have hinv0 : bs ++ encodeVarintAux 10 val = bs ++ encodeVarint val := rfl
  let Fcs : SepProp :=
    ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
      A.pool ∗ stackAt (sp - 48#64) doReserveStack ∗ F
  refine step_encVarint_prologue_trap b ext val v cap ptr sp v48 v40 v32 v24 v16 v8 bs
    (F := vecU8Buf A cap ptr bs ∗ A.pool ∗ stackAt (sp - 48#64) doReserveStack ∗ F)
    hpc hrun hsp halign hx0 hx1 (by rw [hP]; ac_rfl)
    fun s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx8_1 hx9_1 hcs1 => ?_
  have hlt0 := curBs_length_lt_cap hinv0 hle
  cases hbr0 : val.ult 128#64
  · simp only [hbr0, Bool.false_eq_true, ↓reduceIte] at hpc1
    have hinv1 := encodeVarint_inv_next hbr0 hinv0
    refine step_encVarint_s1_trap b A ext val v cap ptr bs hlt0 (F := Fcs)
      hpc1 hrun1 hx0_1 hx1_1 hx8_1 hx9_1 hcs1 (by dsimp [Fcs]; ac_rfl)
      fun s2 hpc2 hrun2 hsp2 htr2 hx0_2 hx1_2 hx8_2 hx9_2 hx10_2 hcs2 => ?_
    have hlt1 := curBs_length_lt_cap hinv1 hle
    cases hbr1 : (val >>> 7).ult 128#64
    · simp only [hbr1, Bool.false_eq_true, ↓reduceIte] at hpc2 hx0_2
      have hinv2 := encodeVarint_inv_next hbr1 hinv1
      rw [ushr_ushr_7 val 7 14] at hinv2
      refine step_encVarint_s2_trap b A ext val v cap ptr _ hlt1 (F := Fcs)
        hpc2 hrun2 hx0_2 hx1_2 hx8_2 hx9_2 hx10_2 hcs2 rfl
        fun s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx1_3 hx8_3 hx9_3 hx10_3 hcs3 => ?_
      have hlt2 := curBs_length_lt_cap hinv2 hle
      cases hbr2 : (val >>> 14).ult 128#64
      · simp only [hbr2, Bool.false_eq_true, ↓reduceIte] at hpc3 hx0_3
        have hinv3 := encodeVarint_inv_next hbr2 hinv2
        rw [ushr_ushr_7 val 14 21] at hinv3
        refine step_encVarint_s3_trap b A ext val v cap ptr _ hlt2 (F := Fcs)
          hpc3 hrun3 hx0_3 hx1_3 hx8_3 hx9_3 hx10_3 hcs3 rfl
          fun s4 hpc4 hrun4 hsp4 htr4 hx0_4 hx1_4 hx8_4 hx9_4 hx12_4 hcs4 => ?_
        have hlt3 := curBs_length_lt_cap hinv3 hle
        cases hbr3 : (val >>> 21).ult 128#64
        · simp only [hbr3, Bool.false_eq_true, ↓reduceIte] at hpc4 hx0_4
          have hinv4 := encodeVarint_inv_next hbr3 hinv3
          rw [ushr_ushr_7 val 21 28] at hinv4
          refine step_encVarint_s4_trap b A ext val v cap ptr _ hlt3 (F := Fcs)
            hpc4 hrun4 hx0_4 hx1_4 hx8_4 hx9_4 hx12_4 hcs4 rfl
            fun s5 hpc5 hrun5 hsp5 htr5 hx0_5 hx1_5 hx8_5 hx9_5 hx10_5 hx11_5 hx12_5 hcs5 => ?_
          have hlt4 := curBs_length_lt_cap hinv4 hle
          cases hbr4 : (val >>> 28).ult 128#64
          · simp only [hbr4, Bool.false_eq_true, ↓reduceIte] at hpc5 hx0_5
            have hinv5 := encodeVarint_inv_next hbr4 hinv4
            rw [ushr_ushr_7 val 28 35] at hinv5
            refine step_encVarint_s5_trap b A ext val v cap ptr _ hlt4 (F := Fcs)
              hpc5 hrun5 hx0_5 hx1_5 hx8_5 hx9_5 hx10_5 hx11_5 hx12_5 hcs5 rfl
              fun s6 hpc6 hrun6 hsp6 htr6 hx0_6 hx1_6 hx8_6 hx9_6 hx10_6 hx11_6 hx12_6 hcs6 => ?_
            have hlt5 := curBs_length_lt_cap hinv5 hle
            cases hbr5 : (val >>> 35).ult 128#64
            · simp only [hbr5, Bool.false_eq_true, ↓reduceIte] at hpc6 hx0_6
              have hinv6 := encodeVarint_inv_next hbr5 hinv5
              rw [ushr_ushr_7 val 35 42] at hinv6
              refine step_encVarint_s6_trap b A ext val v cap ptr _ hlt5 (F := Fcs)
                hpc6 hrun6 hx0_6 hx1_6 hx8_6 hx9_6 hx10_6 hx11_6 hx12_6 hcs6 rfl
                fun s7 hpc7 hrun7 hsp7 htr7 hx0_7 hx1_7 hx8_7 hx9_7 hx11_7 hx12_7 hcs7 => ?_
              have hlt6 := curBs_length_lt_cap hinv6 hle
              cases hbr6 : (val >>> 42).ult 128#64
              · simp only [hbr6, Bool.false_eq_true, ↓reduceIte] at hpc7 hx0_7
                have hinv7 := encodeVarint_inv_next hbr6 hinv6
                rw [ushr_ushr_7 val 42 49] at hinv7
                refine step_encVarint_s7_trap b A ext val v cap ptr _ hlt6 (F := Fcs)
                  hpc7 hrun7 hx0_7 hx1_7 hx8_7 hx9_7 hx11_7 hx12_7 hcs7 rfl
                  fun s8 hpc8 hrun8 hsp8 htr8 hx0_8 hx1_8 hx8_8 hx9_8 hx10_8 hx11_8 hx12_8 hcs8 => ?_
                have hlt7 := curBs_length_lt_cap hinv7 hle
                cases hbr7 : (val >>> 49).ult 128#64
                · simp only [hbr7, Bool.false_eq_true, ↓reduceIte] at hpc8 hx0_8
                  have hinv8 := encodeVarint_inv_next hbr7 hinv7
                  rw [ushr_ushr_7 val 49 56] at hinv8
                  refine step_encVarint_s8_trap b A ext val v cap ptr _ hlt7 (F := Fcs)
                    hpc8 hrun8 hx0_8 hx1_8 hx8_8 hx9_8 hx10_8 hx11_8 hx12_8 hcs8 rfl
                    fun s9 hpc9 hrun9 hsp9 htr9 hx0_9 hx1_9 hx8_9 hx9_9 hx10_9 hx12_9 hcs9 => ?_
                  have hlt8 := curBs_length_lt_cap hinv8 hle
                  cases hbr8 : (val >>> 56).ult 128#64
                  · simp only [hbr8, Bool.false_eq_true, ↓reduceIte] at hpc9 hx0_9
                    have hinv9 := encodeVarint_inv_next hbr8 hinv8
                    rw [ushr_ushr_7 val 56 63] at hinv9
                    refine step_encVarint_s9_trap b A ext val v cap ptr _ hlt8 hbr8 (F := Fcs)
                      hpc9 hrun9 hx1_9 hx8_9 hx9_9 hx10_9 hx12_9 hcs9 rfl
                      fun s10 hpc10 hrun10 hsp10 htr10 hx0_10 hx1_10 hx8_10 hx9_10 hcs10 => ?_
                    have hlt9 := curBs_length_lt_cap hinv9 hle
                    have hdone9 := encodeVarint_inv_done (shr63_ult_128 val) hinv9
                    refine step_encVarint_final_trap b A ext (val >>> 63) v cap ptr sp v48 v40 _ hlt9 (F := F)
                      hpc10 hrun10 (by rw [hsp10, hsp9, hsp8, hsp7, hsp6, hsp5, hsp4, hsp3, hsp2, hsp1]) halign
                      (by rw [htr10, htr9, htr8, htr7, htr6, htr5, htr4, htr3, htr2, htr1]) hx0_10 hx1_10 hx8_10 hx9_10 hcs10
                      (by dsimp [Fcs]; ac_rfl) fun sf hpcf hrunf hspf htrf hcsf => ?_
                    rw [hdone9]
                    exact hnext sf hpcf hrunf hspf htrf hcsf
                  · simp only [hbr8, ↓reduceIte] at hpc9 hx0_9
                    have hdone8 := encodeVarint_inv_done hbr8 hinv8
                    refine step_encVarint_final_trap b A ext (val >>> 56) v cap ptr sp v48 v40 _ hlt8 (F := F)
                      hpc9 hrun9 (by rw [hsp9, hsp8, hsp7, hsp6, hsp5, hsp4, hsp3, hsp2, hsp1]) halign
                      (by rw [htr9, htr8, htr7, htr6, htr5, htr4, htr3, htr2, htr1]) hx0_9 hx1_9 hx8_9 hx9_9 hcs9
                      (by dsimp [Fcs]; ac_rfl) fun sf hpcf hrunf hspf htrf hcsf => ?_
                    rw [hdone8]
                    exact hnext sf hpcf hrunf hspf htrf hcsf
                · simp only [hbr7, ↓reduceIte] at hpc8 hx0_8
                  have hdone7 := encodeVarint_inv_done hbr7 hinv7
                  refine step_encVarint_final_trap b A ext (val >>> 49) v cap ptr sp v48 v40 _ hlt7 (F := F)
                    hpc8 hrun8 (by rw [hsp8, hsp7, hsp6, hsp5, hsp4, hsp3, hsp2, hsp1]) halign
                    (by rw [htr8, htr7, htr6, htr5, htr4, htr3, htr2, htr1]) hx0_8 hx1_8 hx8_8 hx9_8 hcs8
                    (by dsimp [Fcs]; ac_rfl) fun sf hpcf hrunf hspf htrf hcsf => ?_
                  rw [hdone7]
                  exact hnext sf hpcf hrunf hspf htrf hcsf
              · simp only [hbr6, ↓reduceIte] at hpc7 hx0_7
                have hdone6 := encodeVarint_inv_done hbr6 hinv6
                refine step_encVarint_final_trap b A ext (val >>> 42) v cap ptr sp v48 v40 _ hlt6 (F := F)
                  hpc7 hrun7 (by rw [hsp7, hsp6, hsp5, hsp4, hsp3, hsp2, hsp1]) halign
                  (by rw [htr7, htr6, htr5, htr4, htr3, htr2, htr1]) hx0_7 hx1_7 hx8_7 hx9_7 hcs7
                  (by dsimp [Fcs]; ac_rfl) fun sf hpcf hrunf hspf htrf hcsf => ?_
                rw [hdone6]
                exact hnext sf hpcf hrunf hspf htrf hcsf
            · simp only [hbr5, ↓reduceIte] at hpc6 hx0_6
              have hdone5 := encodeVarint_inv_done hbr5 hinv5
              refine step_encVarint_final_trap b A ext (val >>> 35) v cap ptr sp v48 v40 _ hlt5 (F := F)
                hpc6 hrun6 (by rw [hsp6, hsp5, hsp4, hsp3, hsp2, hsp1]) halign
                (by rw [htr6, htr5, htr4, htr3, htr2, htr1]) hx0_6 hx1_6 hx8_6 hx9_6 hcs6
                (by dsimp [Fcs]; ac_rfl) fun sf hpcf hrunf hspf htrf hcsf => ?_
              rw [hdone5]
              exact hnext sf hpcf hrunf hspf htrf hcsf
          · simp only [hbr4, ↓reduceIte] at hpc5 hx0_5
            have hdone4 := encodeVarint_inv_done hbr4 hinv4
            refine step_encVarint_final_trap b A ext (val >>> 28) v cap ptr sp v48 v40 _ hlt4 (F := F)
              hpc5 hrun5 (by rw [hsp5, hsp4, hsp3, hsp2, hsp1]) halign
              (by rw [htr5, htr4, htr3, htr2, htr1]) hx0_5 hx1_5 hx8_5 hx9_5 hcs5
              (by dsimp [Fcs]; ac_rfl) fun sf hpcf hrunf hspf htrf hcsf => ?_
            rw [hdone4]
            exact hnext sf hpcf hrunf hspf htrf hcsf
        · simp only [hbr3, ↓reduceIte] at hpc4 hx0_4
          have hdone3 := encodeVarint_inv_done hbr3 hinv3
          refine step_encVarint_final_trap b A ext (val >>> 21) v cap ptr sp v48 v40 _ hlt3 (F := F)
            hpc4 hrun4 (by rw [hsp4, hsp3, hsp2, hsp1]) halign
            (by rw [htr4, htr3, htr2, htr1]) hx0_4 hx1_4 hx8_4 hx9_4 hcs4
            (by dsimp [Fcs]; ac_rfl) fun sf hpcf hrunf hspf htrf hcsf => ?_
          rw [hdone3]
          exact hnext sf hpcf hrunf hspf htrf hcsf
      · simp only [hbr2, ↓reduceIte] at hpc3 hx0_3
        have hdone2 := encodeVarint_inv_done hbr2 hinv2
        refine step_encVarint_final_trap b A ext (val >>> 14) v cap ptr sp v48 v40 _ hlt2 (F := F)
          hpc3 hrun3 (by rw [hsp3, hsp2, hsp1]) halign
          (by rw [htr3, htr2, htr1]) hx0_3 hx1_3 hx8_3 hx9_3 hcs3
          (by dsimp [Fcs]; ac_rfl) fun sf hpcf hrunf hspf htrf hcsf => ?_
        rw [hdone2]
        exact hnext sf hpcf hrunf hspf htrf hcsf
    · simp only [hbr1, ↓reduceIte] at hpc2 hx0_2
      have hdone1 := encodeVarint_inv_done hbr1 hinv1
      refine step_encVarint_final_trap b A ext (val >>> 7) v cap ptr sp v48 v40 _ hlt1 (F := F)
        hpc2 hrun2 (by rw [hsp2, hsp1]) halign
        (by rw [htr2, htr1]) hx0_2 hx1_2 hx8_2 hx9_2 hcs2
        (by dsimp [Fcs]; ac_rfl) fun sf hpcf hrunf hspf htrf hcsf => ?_
      rw [hdone1]
      exact hnext sf hpcf hrunf hspf htrf hcsf
  · simp only [hbr0, ↓reduceIte] at hpc1
    have hdone0 := encodeVarint_inv_done hbr0 hinv0
    refine step_encVarint_final_trap b A ext val v cap ptr sp v48 v40 _ hlt0 (F := F)
      hpc1 hrun1 hsp1 halign htr1 hx0_1 hx1_1 hx8_1 hx9_1 hcs1
      (by ac_rfl) fun sf hpcf hrunf hspf htrf hcsf => ?_
    rw [hdone0]
    exact hnext sf hpcf hrunf hspf htrf hcsf

theorem step_encVarint_noGrow (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (val v cap ptr sp v48 v40 v32 v24 v16 v8 : BitVec 64) (bs : List (BitVec 8))
    (hle : bs.length + (encodeVarint val).length ≤ cap.toNat)
    {s0 : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeVarintName)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s0.readReg64 .x0 = val)
    (hx1 : s0.readReg64 .x1 = v)
    (hP : P = ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Buf A cap ptr bs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      ((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
      ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8) ∗
      A.pool ∗ stackAt (sp - 48#64) doReserveStack) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf →
      Q sf (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bs ++ encodeVarint val).length) ∗
        vecU8Buf A cap ptr (bs ++ encodeVarint val) ∗
        ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
        ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
        A.pool ∗ stackAt (sp - 48#64) doReserveStack) ∗ F)) :
    SepWPp (tripleRatchetProgAt b C ctl abs) (s0.readReg64 .lr) s0 P Q Qp :=
  step_encVarint_noGrow_trap b A (tripleRatchetExterns C ctl abs) val v cap ptr sp v48 v40 v32 v24 v16 v8 bs hle hpc hrun hsp halign hx0 hx1 hP hnext
def encodeVarintNoGrowSpec (A : RustAlloc) : Spec EncodeVarintGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.val ∧ s.readReg64 .x1 = x.v ∧
      x.bs.length + (encodeVarint x.val).length ≤ x.cap.toNat⌝ ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp encodeVarintStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      vecU8At A x.v x.cap x.ptr (x.bs ++ encodeVarint x.val) ∗
      A.pool ∗ stackAt s0.sp encodeVarintStack

theorem encodeVarintNoGrow_fnAddr_ok_trap (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr encodeVarintName)
      (encodeVarintNoGrowSpec A) := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp_align
  dsimp only [encodeVarintNoGrowSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hle⟩, hpre⟩
  refine ⟨vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s0.sp encodeVarintStack, R, hpre, ?_⟩
  conv =>
    arg 4
    rw [vecU8At_eq_header_sep_buf, vecHeader, stackAt_encodeVarint_eq]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun v48 => SepWPp.exists_elim fun v40 =>
    SepWPp.exists_elim fun v32 => SepWPp.exists_elim fun v24 =>
    SepWPp.exists_elim fun v16 => SepWPp.exists_elim fun v8 => ?_
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simpa [State.spAligned, beq_iff_eq] using hsp_align
  refine step_encVarint_noGrow_trap b A ext x.val x.v x.cap x.ptr s0.sp
    v48 v40 v32 v24 v16 v8 x.bs hle (F := emp) hpc hrun rfl halign hx0 hx1
    (by simp only [sepConj_emp]; ac_rfl)
    fun sf _ _ hspf htrf hcsf => ⟨fun hm => ?_, hspf, hcsf⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htrf, ?_⟩
  rw [vecU8At_eq_header_sep_buf, vecHeader, stackAt_encodeVarint_eq]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
  refine ⟨v48, v40, s0.readReg64 .fp, s0.readReg64 .lr, s0.readReg64 .x20, s0.readReg64 .x19, ?_⟩
  have heq :
      ((((x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
          ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 (x.bs ++ encodeVarint x.val).length) ∗
          vecU8Buf A x.cap x.ptr (x.bs ++ encodeVarint x.val) ∗
          ((s0.sp - 48#64) ↦₆₄ v48) ∗ ((s0.sp - 40#64) ↦₆₄ v40) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
          A.pool ∗ stackAt (s0.sp - 48#64) doReserveStack) ∗ emp) ∗ R) =
      ((((x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
          ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 (x.bs ++ encodeVarint x.val).length)) ∗
          vecU8Buf A x.cap x.ptr (x.bs ++ encodeVarint x.val)) ∗
        A.pool ∗
        (stackAt (s0.sp - 48#64) doReserveStack ∗
          (((s0.sp - 48#64) ↦₆₄ v48) ∗ ((s0.sp - 40#64) ↦₆₄ v40) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))) ∗ R := by
    simp only [sepConj_emp]; ac_rfl
  exact heq ▸ hm

theorem encodeVarintNoGrow_fnAddr_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr encodeVarintName)
      (encodeVarintNoGrowSpec A) :=
  encodeVarintNoGrow_fnAddr_ok_trap b A (tripleRatchetExterns C ctl abs)

theorem encodeVarintNoGrow_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs) (b + 0x30a0#64) (encodeVarintNoGrowSpec A) := by
  have hfn : (tripleRatchetProgAt b C ctl abs).fnAddr encodeVarintName = b + 0x30a0#64 := by
    unfold tripleRatchetProgAt
    rw [Program.fnAddr_rebase, libsignalSessionCode_fnOff_0x30a0]
  rw [← hfn]
  exact encodeVarintNoGrow_fnAddr_ok b C A ctl abs

theorem encodeVarintNoGrow_ok_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) :
    subroutine_ok (trTrapProgAt b C abs) (b + 0x30a0#64) (encodeVarintNoGrowSpec A) := by
  have hfn : (trTrapProgAt b C abs).fnAddr encodeVarintName = b + 0x30a0#64 := by
    unfold trTrapProgAt
    rw [Program.fnAddr_rebase, libsignalSessionCode_fnOff_0x30a0]
  rw [← hfn]
  exact encodeVarintNoGrow_fnAddr_ok_trap b A (trTrapExterns C abs)

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncode
