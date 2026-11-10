/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5Iface
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSites
import LibsignalBinary.Specifications.AsmConstants

/-!
# Stack/Heap Decomposition and `memcpy` Helpers for `main` M5 Moves

Decomposes `dirAt` and `storesAt` into stack words (`DirWords`, `StoresWords`) and detached
heap/rodata ownership (`dirHeap`, `storesHeap`), bridges `storesStackAt` to 320-byte `memcpy`
slices, and connects `locals fsp (m5Cells …)` to `locals fsp (m5LoopCells … 0)`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.CodeLayout

namespace M5MovesHelpers

/-! ## 1. `SepWPp`, SIMD Q-Register, and State-Preservation Helpers -/

theorem sepWPp_exists_left {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {Φ : α → SepProp} {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ x : α, SepWPp prog ret s (Φ x ∗ F) Q Qp oom) :
    SepWPp prog ret s ((∃∗ x : α, Φ x) ∗ F) Q Qp oom := by
  intro R hm hL
  rw [sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨x, hmx⟩
  exact h x R (by simpa only [sepConj_assoc] using hmx) hL

theorem sepWP_seq_inImage_frame {prog : Program} {img : Obj.Image} {mid ret : BitVec 64}
    {s : State} {P_in P P' F : SepProp} {post : State → Prop}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : ImgCallInv img s)
    (hP : P_in ⊢ P ∗ F)
    (h : SepWP prog mid s P (fun s1 P1 => post s1 ∧ P1 = P') (fun _ => ⌜False⌝))
    (hk : ∀ s1 : State, ImgCallInv img s1 → s1.pc = mid → s1.status = .Running → post s1 →
      SepWPp prog ret s1 (P' ∗ F) Q Qp oom) :
    SepWPp prog ret s P_in Q Qp oom := by
  intro R hm hL
  have hm0 : s.mem ⊨ P ∗ (F ∗ R) := by
    simpa only [sepConj_assoc] using Satisfies.mono (sepConj_mono_left hP) hm
  rcases h.elim hm0 hL with ⟨s1, hsteps, ⟨hpc1, hrun1, P1, hm1, hpost1, rfl⟩ | ⟨_, hfalse⟩⟩
  · obtain ⟨sf, hsteps2, hout⟩ :=
      hk s1 (hinv.of_steps hsteps) hpc1 hrun1 hpost1 R
        (by simpa only [sepConj_assoc] using hm1) (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps2, hout⟩
  · exact (not_satisfies_false_sepConj hfalse).elim

theorem spAligned_of_s0 {s0 s : State}
    (h0 : s0.spAligned = true) (hsp : s.sp = s0.sp - 0x4e0#64) :
    s.spAligned = true := by
  simp only [State.spAligned, beq_iff_eq] at h0 ⊢
  rw [hsp]
  bv_bits

@[simp, arm64_norm]
theorem extractLsb_append_lo (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 0 64 = lo := by
  bv_bits

@[simp, arm64_norm]
theorem extractLsb_append_hi (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 64 64 = hi := by
  bv_bits

@[simp, arm64_norm]
theorem calleeSavedVRegs_writeVReg128_q0 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 0#5 v) = calleeSavedVRegs s := by
  simp [calleeSavedVRegs, State.writeVReg128, VRegFile.calleeSaved, VRegFile.write, VRegFile.read]

@[simp, arm64_norm]
theorem calleeSavedVRegs_writeVReg128_q1 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 1#5 v) = calleeSavedVRegs s := by
  simp [calleeSavedVRegs, State.writeVReg128, VRegFile.calleeSaved, VRegFile.write, VRegFile.read]

@[simp, arm64_norm]
theorem calleeSavedVRegs_writeVReg128_q2 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 2#5 v) = calleeSavedVRegs s := by
  simp [calleeSavedVRegs, State.writeVReg128, VRegFile.calleeSaved, VRegFile.write, VRegFile.read]

@[simp, arm64_norm]
theorem calleeSavedVRegs_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    calleeSavedVRegs (s.writeReg64 r v) = calleeSavedVRegs s := by
  cases s; cases r <;> rfl

@[simp, arm64_norm]
theorem calleeSavedVRegs_setPC (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := by
  cases s; rfl

@[simp, arm64_norm]
theorem calleeSavedVRegs_setMem (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by
  cases s; rfl

@[simp, arm64_norm]
theorem fs_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).fs = s.fs := by
  cases s; cases r <;> rfl

@[simp, arm64_norm]
theorem fs_writeVReg128 (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).fs = s.fs := by
  cases s; rfl

@[simp, arm64_norm]
theorem fs_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).fs = s.fs := by
  cases s; rfl

@[simp, arm64_norm]
theorem fs_setMem (s : State) (m : Memory) :
    (s.setMem m).fs = s.fs := by
  cases s; rfl

/-! ## 2. Word/Byte Decomposition of `dirAt`, `storesAt`, and `vecU8` -/

/-- The five 64-bit stack words of a `Dir` struct (`40 = 0x28` bytes). -/
structure DirWords where
  w0 : BitVec 64
  w1 : BitVec 64
  w2 : BitVec 64
  w3 : BitVec 64
  w4 : BitVec 64

/-- The eight `DirWords` of a `Stores` struct (`320 = 0x140` bytes). -/
structure StoresWords where
  d0 : DirWords
  d1 : DirWords
  d2 : DirWords
  d3 : DirWords
  d4 : DirWords
  d5 : DirWords
  d6 : DirWords
  d7 : DirWords

/-- Stack footprint (`40` bytes = five `↦₆₄` words) of one `Dir` at `d`. -/
def dirStackAt (d : BitVec 64) (w : DirWords) : SepProp :=
  (d ↦₆₄ w.w0) ∗ ((d + 0x08#64) ↦₆₄ w.w1) ∗ ((d + 0x10#64) ↦₆₄ w.w2) ∗
    ((d + 0x18#64) ↦₆₄ w.w3) ∗ ((d + 0x20#64) ↦₆₄ w.w4)

/-- Detached heap + rodata ownership of one `Dir` given its five stack words `w`. -/
def dirHeap (A : RustAlloc) (w : DirWords) (g : DirGhost) : SepProp :=
  ⌜w.w2 = BitVec.ofNat 64 g.changed.length ∧ w.w4 = BitVec.ofNat 64 g.path.length⌝ ∗
    RustHeap.vecBuf A 48 8 (dirEntryAt A) w.w0 w.w1 g.changed ∗
    (w.w3 ↦ᵣ g.path)

theorem dirAt_unpack (A : RustAlloc) (d : BitVec 64) (g : DirGhost) :
    dirAt A d g ⊢ ∃∗ w : DirWords, dirStackAt d w ∗ dirHeap A w g := by
  unfold dirAt vecOf vecAt vecHeader strRefAt
  have hlenOff : d + 0x18#64 + asm64% boxSliceLenOff = d + 0x20#64 := by
    bv_arith
  rw [hlenOff]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro p
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right
    ⟨cap, ptr, BitVec.ofNat 64 g.changed.length, p, BitVec.ofNat 64 g.path.length⟩ ?_
  unfold dirStackAt dirHeap
  have hpure : ⌜BitVec.ofNat 64 g.changed.length = BitVec.ofNat 64 g.changed.length ∧
      BitVec.ofNat 64 g.path.length = BitVec.ofNat 64 g.path.length⌝ = (emp : SepProp) := by
    simp
  rw [hpure, emp_sepConj]
  exact Entails.of_eq (by ac_rfl)

theorem dirAt_repack (A : RustAlloc) (d : BitVec 64) (w : DirWords) (g : DirGhost) :
    dirStackAt d w ∗ dirHeap A w g ⊢ dirAt A d g := by
  unfold dirHeap
  have hassoc :
      dirStackAt d w ∗
        (⌜w.w2 = BitVec.ofNat 64 g.changed.length ∧ w.w4 = BitVec.ofNat 64 g.path.length⌝ ∗
          RustHeap.vecBuf A 48 8 (dirEntryAt A) w.w0 w.w1 g.changed ∗ (w.w3 ↦ᵣ g.path)) =
      ⌜w.w2 = BitVec.ofNat 64 g.changed.length ∧ w.w4 = BitVec.ofNat 64 g.path.length⌝ ∗
        (dirStackAt d w ∗ RustHeap.vecBuf A 48 8 (dirEntryAt A) w.w0 w.w1 g.changed ∗
          (w.w3 ↦ᵣ g.path)) := by ac_rfl
  rw [hassoc]
  apply Entails.pure_left
  rintro ⟨hw2, hw4⟩
  unfold dirAt vecOf vecAt vecHeader strRefAt dirStackAt
  have hlenOff : d + 0x18#64 + asm64% boxSliceLenOff = d + 0x20#64 := by
    bv_arith
  rw [hlenOff, hw2, hw4]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_right w.w3 (Entails.sepExists_right w.w0 (Entails.sepExists_right w.w1 ?_))
  exact Entails.of_eq (by ac_rfl)

/-- Stack footprint (`320 = 0x140` bytes = eight `Dir`s) of a `Stores` at `a`. -/
def storesStackAt (a : BitVec 64) (ws : StoresWords) : SepProp :=
  dirStackAt a ws.d0 ∗
    dirStackAt (a + 0x28#64) ws.d1 ∗
    dirStackAt (a + 0x50#64) ws.d2 ∗
    dirStackAt (a + 0x78#64) ws.d3 ∗
    dirStackAt (a + 0xa0#64) ws.d4 ∗
    dirStackAt (a + 0xc8#64) ws.d5 ∗
    dirStackAt (a + 0xf0#64) ws.d6 ∗
    dirStackAt (a + 0x118#64) ws.d7

/-- Detached heap + rodata ownership of all eight `Dir`s of `g`. -/
def storesHeap (A : RustAlloc) (ws : StoresWords) (g : StoresGhost) : SepProp :=
  dirHeap A ws.d0 g.identity.own ∗
    dirHeap A ws.d1 g.identity.peers ∗
    dirHeap A ws.d2 g.signed ∗
    dirHeap A ws.d3 g.kyber.oneTime ∗
    dirHeap A ws.d4 g.kyber.lastResort ∗
    dirHeap A ws.d5 g.oneTime ∗
    dirHeap A ws.d6 g.sessions ∗
    dirHeap A ws.d7 g.pub

theorem storesAt_unpack (A : RustAlloc) (a : BitVec 64) (g : StoresGhost) :
    storesAt A a g ⊢ ∃∗ ws : StoresWords, storesStackAt a ws ∗ storesHeap A ws g := by
  unfold storesAt
  refine Entails.trans
    (sepConj_mono (dirAt_unpack A a g.identity.own)
      (sepConj_mono (dirAt_unpack A (a + 0x28#64) g.identity.peers)
        (sepConj_mono (dirAt_unpack A (a + 0x50#64) g.signed)
          (sepConj_mono (dirAt_unpack A (a + 0x78#64) g.kyber.oneTime)
            (sepConj_mono (dirAt_unpack A (a + 0xa0#64) g.kyber.lastResort)
              (sepConj_mono (dirAt_unpack A (a + 0xc8#64) g.oneTime)
                (sepConj_mono (dirAt_unpack A (a + 0xf0#64) g.sessions)
                  (dirAt_unpack A (a + 0x118#64) g.pub)))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w7
  apply Entails.sepExists_elim; intro w6
  apply Entails.sepExists_elim; intro w5
  apply Entails.sepExists_elim; intro w4
  apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w1
  apply Entails.sepExists_elim; intro w0
  refine Entails.sepExists_right ⟨w0, w1, w2, w3, w4, w5, w6, w7⟩ ?_
  unfold storesStackAt storesHeap
  exact Entails.of_eq (by dsimp only; ac_rfl)

theorem storesAt_repack (A : RustAlloc) (a : BitVec 64) (ws : StoresWords) (g : StoresGhost) :
    storesStackAt a ws ∗ storesHeap A ws g ⊢ storesAt A a g := by
  unfold storesStackAt storesHeap storesAt
  refine Entails.trans (Entails.of_eq (show
    (dirStackAt a ws.d0 ∗ dirStackAt (a + 0x28#64) ws.d1 ∗ dirStackAt (a + 0x50#64) ws.d2 ∗
      dirStackAt (a + 0x78#64) ws.d3 ∗ dirStackAt (a + 0xa0#64) ws.d4 ∗
      dirStackAt (a + 0xc8#64) ws.d5 ∗ dirStackAt (a + 0xf0#64) ws.d6 ∗
      dirStackAt (a + 0x118#64) ws.d7) ∗
    (dirHeap A ws.d0 g.identity.own ∗ dirHeap A ws.d1 g.identity.peers ∗
      dirHeap A ws.d2 g.signed ∗ dirHeap A ws.d3 g.kyber.oneTime ∗
      dirHeap A ws.d4 g.kyber.lastResort ∗ dirHeap A ws.d5 g.oneTime ∗
      dirHeap A ws.d6 g.sessions ∗ dirHeap A ws.d7 g.pub) =
    (dirStackAt a ws.d0 ∗ dirHeap A ws.d0 g.identity.own) ∗
    (dirStackAt (a + 0x28#64) ws.d1 ∗ dirHeap A ws.d1 g.identity.peers) ∗
    (dirStackAt (a + 0x50#64) ws.d2 ∗ dirHeap A ws.d2 g.signed) ∗
    (dirStackAt (a + 0x78#64) ws.d3 ∗ dirHeap A ws.d3 g.kyber.oneTime) ∗
    (dirStackAt (a + 0xa0#64) ws.d4 ∗ dirHeap A ws.d4 g.kyber.lastResort) ∗
    (dirStackAt (a + 0xc8#64) ws.d5 ∗ dirHeap A ws.d5 g.oneTime) ∗
    (dirStackAt (a + 0xf0#64) ws.d6 ∗ dirHeap A ws.d6 g.sessions) ∗
    (dirStackAt (a + 0x118#64) ws.d7 ∗ dirHeap A ws.d7 g.pub) by ac_rfl)) ?_
  exact sepConj_mono (dirAt_repack A a ws.d0 g.identity.own)
    (sepConj_mono (dirAt_repack A (a + 0x28#64) ws.d1 g.identity.peers)
      (sepConj_mono (dirAt_repack A (a + 0x50#64) ws.d2 g.signed)
        (sepConj_mono (dirAt_repack A (a + 0x78#64) ws.d3 g.kyber.oneTime)
          (sepConj_mono (dirAt_repack A (a + 0xa0#64) ws.d4 g.kyber.lastResort)
            (sepConj_mono (dirAt_repack A (a + 0xc8#64) ws.d5 g.oneTime)
              (sepConj_mono (dirAt_repack A (a + 0xf0#64) ws.d6 g.sessions)
                (dirAt_repack A (a + 0x118#64) ws.d7 g.pub)))))))

/-- 40 little-endian bytes of a `DirWords`. -/
def dirBytes (w : DirWords) : List (BitVec 8) :=
  unpack64 w.w0 ++ (unpack64 w.w1 ++ (unpack64 w.w2 ++ (unpack64 w.w3 ++ unpack64 w.w4)))

@[simp]
theorem dirBytes_length (w : DirWords) : (dirBytes w).length = 0x28 := by
  simp [dirBytes]

theorem dirStackAt_eq_bytes (d : BitVec 64) (w : DirWords) :
    dirStackAt d w = (d ↦ₛ dirBytes w) := by
  unfold dirStackAt dirBytes
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]
  simp only [unpack64_length]
  rw [← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes,
      ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes,
      ← pointsTo64_eq_pointsToBytes]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

/-- 320 little-endian bytes of a `StoresWords`. -/
def storesBytes (ws : StoresWords) : List (BitVec 8) :=
  dirBytes ws.d0 ++ (dirBytes ws.d1 ++ (dirBytes ws.d2 ++ (dirBytes ws.d3 ++
    (dirBytes ws.d4 ++ (dirBytes ws.d5 ++ (dirBytes ws.d6 ++ dirBytes ws.d7))))))

@[simp]
theorem storesBytes_length (ws : StoresWords) : (storesBytes ws).length = 0x140 := by
  simp [storesBytes]

theorem storesStackAt_eq_bytes (a : BitVec 64) (ws : StoresWords) :
    storesStackAt a ws = (a ↦ₛ storesBytes ws) := by
  unfold storesStackAt storesBytes
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
      pointsToBytes_append, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]
  simp only [dirBytes_length]
  rw [← dirStackAt_eq_bytes, ← dirStackAt_eq_bytes, ← dirStackAt_eq_bytes,
      ← dirStackAt_eq_bytes, ← dirStackAt_eq_bytes, ← dirStackAt_eq_bytes,
      ← dirStackAt_eq_bytes, ← dirStackAt_eq_bytes]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem pointsTo8_entails_memRegion (a : BitVec 64) (b : BitVec 8) :
    (a ↦₈ b) ⊢ memRegion a 1 := by
  have heq : memRegion a 1 = ∃∗ b' : BitVec 8, a ↦₈ b' :=
    IsBlock.eq (IsBlock.memRegion a 1)
      (IsBlock.sepExists fun b' => IsBlock.pointsTo8 a b')
      fun _ => ⟨fun _ => ⟨_, rfl⟩, fun _ => trivial⟩
  rw [heq]
  exact Entails.sepExists_intro b

theorem pointsToBytes_entails_memRegion :
    ∀ (bs : List (BitVec 8)) (p : BitVec 64), bs.length ≤ 2 ^ 64 →
      (p ↦ₛ bs) ⊢ memRegion p bs.length
  | [], p, _ => by
    rw [pointsToBytes_nil, List.length_nil, memRegion_zero]
    exact Entails.refl _
  | b :: bs, p, hlen => by
    have hlen' : bs.length ≤ 2 ^ 64 := by simp at hlen; omega
    rw [pointsToBytes_cons, List.length_cons,
      show bs.length + 1 = 1 + bs.length by omega,
      memRegion_split p 1 bs.length (by simp at hlen; omega)]
    exact sepConj_mono (pointsTo8_entails_memRegion p b)
      (pointsToBytes_entails_memRegion bs (p + 1#64) hlen')

theorem storesStackAt_entails_memRegion (a : BitVec 64) (ws : StoresWords) :
    storesStackAt a ws ⊢ memRegion a 0x140 := by
  rw [storesStackAt_eq_bytes]
  have h := pointsToBytes_entails_memRegion (storesBytes ws) a (by simp [storesBytes_length])
  rwa [storesBytes_length] at h

theorem memRegion_40_entails_exists_dirWords (d : BitVec 64) :
    memRegion d 0x28 ⊢ ∃∗ w : DirWords, dirStackAt d w := by
  have s1 := memRegion_split d 8 32 (by decide)
  have s2 := memRegion_split (d + 0x08#64) 8 24 (by decide)
  have s3 := memRegion_split (d + 0x10#64) 8 16 (by decide)
  have s4 := memRegion_split (d + 0x18#64) 8 8 (by decide)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd] at s1 s2 s3 s4
  rw [s1, s2, s3, s4,
      ProofLib.memRegion_eight d, ProofLib.memRegion_eight (d + 0x08#64),
      ProofLib.memRegion_eight (d + 0x10#64), ProofLib.memRegion_eight (d + 0x18#64),
      ProofLib.memRegion_eight (d + 0x20#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w4
  apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w1
  apply Entails.sepExists_elim; intro w0
  unfold dirStackAt
  exact Entails.sepExists_right ⟨w0, w1, w2, w3, w4⟩ (Entails.of_eq (by ac_rfl))

theorem memRegion_320_entails_exists_storesWords (a : BitVec 64) :
    memRegion a 0x140 ⊢ ∃∗ ws : StoresWords, storesStackAt a ws := by
  have s1 := memRegion_split a 0x28 0x118 (by decide)
  have s2 := memRegion_split (a + 0x28#64) 0x28 0xf0 (by decide)
  have s3 := memRegion_split (a + 0x50#64) 0x28 0xc8 (by decide)
  have s4 := memRegion_split (a + 0x78#64) 0x28 0xa0 (by decide)
  have s5 := memRegion_split (a + 0xa0#64) 0x28 0x78 (by decide)
  have s6 := memRegion_split (a + 0xc8#64) 0x28 0x50 (by decide)
  have s7 := memRegion_split (a + 0xf0#64) 0x28 0x28 (by decide)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd] at s1 s2 s3 s4 s5 s6 s7
  rw [s1, s2, s3, s4, s5, s6, s7]
  refine Entails.trans
    (sepConj_mono (memRegion_40_entails_exists_dirWords a)
      (sepConj_mono (memRegion_40_entails_exists_dirWords (a + 0x28#64))
        (sepConj_mono (memRegion_40_entails_exists_dirWords (a + 0x50#64))
          (sepConj_mono (memRegion_40_entails_exists_dirWords (a + 0x78#64))
            (sepConj_mono (memRegion_40_entails_exists_dirWords (a + 0xa0#64))
              (sepConj_mono (memRegion_40_entails_exists_dirWords (a + 0xc8#64))
                (sepConj_mono (memRegion_40_entails_exists_dirWords (a + 0xf0#64))
                  (memRegion_40_entails_exists_dirWords (a + 0x118#64))))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro d7
  apply Entails.sepExists_elim; intro d6
  apply Entails.sepExists_elim; intro d5
  apply Entails.sepExists_elim; intro d4
  apply Entails.sepExists_elim; intro d3
  apply Entails.sepExists_elim; intro d2
  apply Entails.sepExists_elim; intro d1
  apply Entails.sepExists_elim; intro d0
  unfold storesStackAt
  exact Entails.sepExists_right ⟨d0, d1, d2, d3, d4, d5, d6, d7⟩ (Entails.of_eq (by ac_rfl))

/-- Unpack `vecU8 A v out` into its 3-word header at `v` plus `ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out`. -/
theorem vecU8_unpack_ownedBytes (A : RustAlloc) (v : BitVec 64) (out : List (BitVec 8)) :
    vecU8 A v out ⊢
      ∃∗ outCap : BitVec 64, ∃∗ outPtr : BitVec 64,
        (v ↦₆₄ outCap) ∗ ((v + 0x08#64) ↦₆₄ outPtr) ∗
          ((v + 0x10#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
          ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out := by
  unfold vecU8
  apply Entails.sepExists_elim; intro outCap
  apply Entails.sepExists_elim; intro outPtr
  refine Entails.sepExists_right outCap (Entails.sepExists_right outPtr ?_)
  unfold vecU8At vecHeader ownedBytes
  have hpure :
      ⌜BitVec.ofNat 64 out.length = BitVec.ofNat 64 out.length ∧
        out.length ≤ outCap.toNat ∧ outCap.toNat < 2 ^ 63 ∧ outPtr ≠ 0⌝ =
      (⌜out.length ≤ outCap.toNat ∧ outCap.toNat < 2 ^ 63 ∧ outPtr ≠ 0⌝ : SepProp) := by
    simp
  rw [hpure]
  exact Entails.of_eq (by ac_rfl)

/-! ## 3. Exact `locals` Open / Mid / Close Bridges (`m5Cells` → `m5LoopCells … 0`) -/

/-- Untouched uninitialized stack sub-gaps inside `locals fsp` during M5's payload moves:
`[0x00, 0x08)`, `[0x28, 0x58)`, `[0x60, 0x78)`, and `[0x450, 0x480)`. -/
def m5LocalsRest (fsp : BitVec 64) : SepProp :=
  memRegion fsp 0x08 ∗
    memRegion (fsp + 0x28#64) 0x30 ∗
    memRegion (fsp + 0x60#64) 0x18 ∗
    memRegion (fsp + 0x450#64) 0x30

/-- Existential bundle produced when opening `locals fsp (m5Cells A fsp inPtr g out)`. -/
structure M5OpenVars where
  ws : StoresWords
  dstWs : StoresWords
  outCap : BitVec 64
  outPtr : BitVec 64
  u08 : BitVec 64
  u10 : BitVec 64
  u18 : BitVec 64
  u20 : BitVec 64

/-- Open `locals fsp (m5Cells A fsp inPtr g out)` into the spill cells, `memcpy` source/destination
slices, `dstWs` words at `fsp + 0x310`, `storesHeap`, `ownedBytes`, and `m5LocalsRest`. -/
theorem m5_locals_open (A : RustAlloc) (fsp inPtr : BitVec 64)
    (g : StoresGhost) (out : List (BitVec 8)) :
    locals fsp (m5Cells A fsp inPtr g out) ⊢
      ∃∗ v : M5OpenVars,
        ((fsp + 0x08#64) ↦₆₄ v.u08) ∗
          ((fsp + 0x10#64) ↦₆₄ v.u10) ∗
          ((fsp + 0x18#64) ↦₆₄ v.u18) ∗
          ((fsp + 0x20#64) ↦₆₄ v.u20) ∗
          ((fsp + 0x58#64) ↦₆₄ inPtr) ∗
          memRegion (fsp + 0x78#64) 0x140 ∗
          ((fsp + 0x1b8#64) ↦ₛ storesBytes v.ws) ∗
          ((fsp + 0x2f8#64) ↦₆₄ v.outCap) ∗
          ((fsp + 0x300#64) ↦₆₄ v.outPtr) ∗
          ((fsp + 0x308#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
          storesStackAt (fsp + 0x310#64) v.dstWs ∗
          m5LocalsRest fsp ∗
          storesHeap A v.ws g ∗
          ownedBytes A v.outCap v.outPtr (BitVec.ofNat 64 out.length) out := by
  have g0 :
      memRegion (fsp + 0#64) 0x58 =
        memRegion fsp 0x08 ∗
          memRegion (fsp + 0x08#64) 8 ∗
          memRegion (fsp + 0x10#64) 8 ∗
          memRegion (fsp + 0x18#64) 8 ∗
          memRegion (fsp + 0x20#64) 8 ∗
          memRegion (fsp + 0x28#64) 0x30 := by
    have s1 := memRegion_split fsp 0x08 0x50 (by decide)
    have s2 := memRegion_split (fsp + 0x08#64) 8 0x48 (by decide)
    have s3 := memRegion_split (fsp + 0x10#64) 8 0x40 (by decide)
    have s4 := memRegion_split (fsp + 0x18#64) 8 0x38 (by decide)
    have s5 := memRegion_split (fsp + 0x20#64) 8 0x30 (by decide)
    simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd] at s1 s2 s3 s4 s5
    rw [BitVec.add_zero, s1, s2, s3, s4, s5]
  have g1 :
      memRegion (fsp + 0x60#64) 0x158 =
        memRegion (fsp + 0x60#64) 0x18 ∗ memRegion (fsp + 0x78#64) 0x140 := by
    have s := memRegion_split (fsp + 0x60#64) 0x18 0x140 (by decide)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at s
    exact s
  have g2 :
      memRegion (fsp + 0x310#64) 0x170 =
        memRegion (fsp + 0x310#64) 0x140 ∗ memRegion (fsp + 0x450#64) 0x30 := by
    have s := memRegion_split (fsp + 0x310#64) 0x140 0x30 (by decide)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at s
    exact s
  dsimp only [locals, m5Cells, localsFrom, cell, runResSize, runOkAt]
  change (memRegion (fsp + 0#64) 0x58 ∗
    ((fsp + 0x58#64) ↦₆₄ inPtr) ∗
    (memRegion (fsp + 0x60#64) 0x158 ∗
      (storesAt A (fsp + 0x1b8#64) g ∗ vecU8 A (fsp + 0x1b8#64 + 0x140#64) out) ∗
      memRegion (fsp + 0x310#64) 0x170)) ⊢ _
  have h2f8 : fsp + 0x1b8#64 + 0x140#64 = fsp + 0x2f8#64 := by bv_arith
  rw [g0, g1, g2, h2f8,
      ProofLib.memRegion_eight (fsp + 0x08#64),
      ProofLib.memRegion_eight (fsp + 0x10#64),
      ProofLib.memRegion_eight (fsp + 0x18#64),
      ProofLib.memRegion_eight (fsp + 0x20#64)]
  refine Entails.trans
    (sepConj_mono_right
      (sepConj_mono_right
        (sepConj_mono_right
          (sepConj_mono
            (sepConj_mono
              (storesAt_unpack A (fsp + 0x1b8#64) g)
              (vecU8_unpack_ownedBytes A (fsp + 0x2f8#64) out))
            (sepConj_mono_left (memRegion_320_entails_exists_storesWords (fsp + 0x310#64))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro dstWs
  apply Entails.sepExists_elim; intro outCap
  apply Entails.sepExists_elim; intro outPtr
  apply Entails.sepExists_elim; intro ws
  apply Entails.sepExists_elim; intro u20
  apply Entails.sepExists_elim; intro u18
  apply Entails.sepExists_elim; intro u10
  apply Entails.sepExists_elim; intro u08
  refine Entails.sepExists_right ⟨ws, dstWs, outCap, outPtr, u08, u10, u18, u20⟩ ?_
  rw [storesStackAt_eq_bytes (fsp + 0x1b8#64) ws]
  have h300 : fsp + 0x2f8#64 + 0x08#64 = fsp + 0x300#64 := by bv_arith
  have h308 : fsp + 0x2f8#64 + 0x10#64 = fsp + 0x308#64 := by bv_arith
  rw [h300, h308]
  unfold m5LocalsRest
  exact Entails.of_eq (by ac_rfl)

/-- After `M+0x73c`'s `memcpy(fsp + 0x78 ← fsp + 0x1b8, 320)`, expose `storesStackAt (fsp + 0x78) ws`
and split `[0x1b8, 0x2f8)` into `memRegion (fsp + 0x1b8) 8`, `[fsp + 0x1c0]`, and
`memRegion (fsp + 0x1c8) 0x130`. -/
theorem m5_post_first_memcpy (fsp : BitVec 64) (ws : StoresWords) :
    ((fsp + 0x78#64) ↦ₛ storesBytes ws) ∗ ((fsp + 0x1b8#64) ↦ₛ storesBytes ws) ⊢
      ∃∗ u1c0 : BitVec 64,
        storesStackAt (fsp + 0x78#64) ws ∗
          ((fsp + 0x1c0#64) ↦₆₄ u1c0) ∗
          memRegion (fsp + 0x1b8#64) 0x08 ∗
          memRegion (fsp + 0x1c8#64) 0x130 := by
  rw [← storesStackAt_eq_bytes (fsp + 0x78#64) ws]
  have hmem : ((fsp + 0x1b8#64) ↦ₛ storesBytes ws) ⊢ memRegion (fsp + 0x1b8#64) 0x140 := by
    have h := pointsToBytes_entails_memRegion (storesBytes ws) (fsp + 0x1b8#64)
      (by simp [storesBytes_length])
    rwa [storesBytes_length] at h
  have s1 := memRegion_split (fsp + 0x1b8#64) 0x08 0x138 (by decide)
  have s2 := memRegion_split (fsp + 0x1c0#64) 0x08 0x130 (by decide)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd] at s1 s2
  refine Entails.trans (sepConj_mono_right hmem) ?_
  rw [s1, s2, ProofLib.memRegion_eight (fsp + 0x1c0#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro u1c0
  exact Entails.sepExists_right u1c0 (Entails.of_eq (by ac_rfl))

/-- Right before `M+0x814`'s `memcpy(fsp + 0x1c8 ← fsp + 0x310, 320)`, merge `[0x1c8, 0x2f8)` with
`[0x2f8, 0x308)` into `memRegion (fsp + 0x1c8) 0x140`, expose `(fsp + 0x310) ↦ₛ storesBytes ws`, and
pack all dead scratch regions (`[0x78, 0x1c8)` and `[0x308, 0x310)`) together with `m5LocalsRest`
into `m5PreMemcpy2Rest fsp`. -/
def m5PreMemcpy2Rest (fsp : BitVec 64) : SepProp :=
  memRegion fsp 0x08 ∗
    memRegion (fsp + 0x28#64) 0x30 ∗
    memRegion (fsp + 0x60#64) 0x168 ∗
    memRegion (fsp + 0x308#64) 0x08 ∗
    memRegion (fsp + 0x450#64) 0x30

theorem m5_pre_second_memcpy (fsp outCap outPtr outLen : BitVec 64) (ws : StoresWords) :
    storesStackAt (fsp + 0x78#64) ws ∗
      memRegion (fsp + 0x1b8#64) 0x08 ∗
      ((fsp + 0x1c0#64) ↦₆₄ 8#64) ∗
      memRegion (fsp + 0x1c8#64) 0x130 ∗
      ((fsp + 0x2f8#64) ↦₆₄ outCap) ∗
      ((fsp + 0x300#64) ↦₆₄ outPtr) ∗
      ((fsp + 0x308#64) ↦₆₄ outLen) ∗
      storesStackAt (fsp + 0x310#64) ws ∗
      m5LocalsRest fsp ⊢
      memRegion (fsp + 0x1c8#64) 0x140 ∗
        ((fsp + 0x310#64) ↦ₛ storesBytes ws) ∗
        m5PreMemcpy2Rest fsp := by
  unfold m5LocalsRest m5PreMemcpy2Rest
  rw [storesStackAt_eq_bytes (fsp + 0x310#64) ws]
  refine Entails.trans
    (sepConj_mono (storesStackAt_entails_memRegion (fsp + 0x78#64) ws)
      (sepConj_mono_right
        (sepConj_mono (pointsTo64_entails_memRegion (fsp + 0x1c0#64) 8#64)
          (sepConj_mono_right
            (sepConj_mono (pointsTo64_entails_memRegion (fsp + 0x2f8#64) outCap)
              (sepConj_mono (pointsTo64_entails_memRegion (fsp + 0x300#64) outPtr)
                (sepConj_mono_left (pointsTo64_entails_memRegion (fsp + 0x308#64) outLen)))))))) ?_
  have mDst :
      memRegion (fsp + 0x1c8#64) 0x140 =
        memRegion (fsp + 0x1c8#64) 0x130 ∗
          memRegion (fsp + 0x2f8#64) 0x08 ∗
          memRegion (fsp + 0x300#64) 0x08 := by
    have s1 := memRegion_split (fsp + 0x1c8#64) 0x130 0x10 (by decide)
    have s2 := memRegion_split (fsp + 0x2f8#64) 0x08 0x08 (by decide)
    simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd] at s1 s2
    rw [s1, s2]
  have mMid :
      memRegion (fsp + 0x60#64) 0x168 =
        memRegion (fsp + 0x60#64) 0x18 ∗
          memRegion (fsp + 0x78#64) 0x140 ∗
          memRegion (fsp + 0x1b8#64) 0x08 ∗
          memRegion (fsp + 0x1c0#64) 0x08 := by
    have s1 := memRegion_split (fsp + 0x60#64) 0x18 0x150 (by decide)
    have s2 := memRegion_split (fsp + 0x78#64) 0x140 0x10 (by decide)
    have s3 := memRegion_split (fsp + 0x1b8#64) 0x08 0x08 (by decide)
    simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd] at s1 s2 s3
    rw [s1, s2, s3]
  rw [mDst, mMid]
  exact Entails.of_eq (by ac_rfl)

/-- After `M+0x814`'s `memcpy(fsp + 0x1c8 ← fsp + 0x310, 320)`, reassemble
`locals fsp (m5LoopCells A fsp outCap outPtr outLen inCap inPtr g 0)`. -/
theorem m5_locals_close (A : RustAlloc)
    (fsp outCap outPtr outLen inCap inPtr : BitVec 64)
    (ws : StoresWords) (g : StoresGhost) :
    ((fsp + 0x08#64) ↦₆₄ outLen) ∗
      ((fsp + 0x10#64) ↦₆₄ outPtr) ∗
      ((fsp + 0x18#64) ↦₆₄ outCap) ∗
      ((fsp + 0x20#64) ↦₆₄ inCap) ∗
      ((fsp + 0x58#64) ↦₆₄ inPtr) ∗
      ((fsp + 0x1c8#64) ↦ₛ storesBytes ws) ∗
      ((fsp + 0x310#64) ↦ₛ storesBytes ws) ∗
      m5PreMemcpy2Rest fsp ∗
      storesHeap A ws g ⊢
      locals fsp (m5LoopCells A fsp outCap outPtr outLen inCap inPtr g 0) := by
  rw [m5LoopCells_zero_eq, ← storesStackAt_eq_bytes (fsp + 0x1c8#64) ws]
  have hsrc : ((fsp + 0x310#64) ↦ₛ storesBytes ws) ⊢ memRegion (fsp + 0x310#64) 0x140 := by
    have h := pointsToBytes_entails_memRegion (storesBytes ws) (fsp + 0x310#64)
      (by simp [storesBytes_length])
    rwa [storesBytes_length] at h
  refine Entails.trans
    (Entails.of_eq (show
      ((fsp + 0x08#64) ↦₆₄ outLen) ∗ ((fsp + 0x10#64) ↦₆₄ outPtr) ∗
        ((fsp + 0x18#64) ↦₆₄ outCap) ∗ ((fsp + 0x20#64) ↦₆₄ inCap) ∗
        ((fsp + 0x58#64) ↦₆₄ inPtr) ∗ storesStackAt (fsp + 0x1c8#64) ws ∗
        ((fsp + 0x310#64) ↦ₛ storesBytes ws) ∗ m5PreMemcpy2Rest fsp ∗ storesHeap A ws g =
      (storesStackAt (fsp + 0x1c8#64) ws ∗ storesHeap A ws g) ∗
        ((fsp + 0x310#64) ↦ₛ storesBytes ws) ∗
        (((fsp + 0x08#64) ↦₆₄ outLen) ∗ ((fsp + 0x10#64) ↦₆₄ outPtr) ∗
          ((fsp + 0x18#64) ↦₆₄ outCap) ∗ ((fsp + 0x20#64) ↦₆₄ inCap) ∗
          ((fsp + 0x58#64) ↦₆₄ inPtr) ∗ m5PreMemcpy2Rest fsp) by ac_rfl)) ?_
  refine Entails.trans
    (sepConj_mono (storesAt_repack A (fsp + 0x1c8#64) ws g) (sepConj_mono_left hsrc)) ?_
  unfold m5PreMemcpy2Rest
  have mTail :
      memRegion (fsp + 0x308#64) 0x178 =
        memRegion (fsp + 0x308#64) 0x08 ∗
          memRegion (fsp + 0x310#64) 0x140 ∗
          memRegion (fsp + 0x450#64) 0x30 := by
    have s1 := memRegion_split (fsp + 0x308#64) 0x08 0x170 (by decide)
    have s2 := memRegion_split (fsp + 0x310#64) 0x140 0x30 (by decide)
    simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd] at s1 s2
    rw [s1, s2]
  dsimp only [locals, m6Cells, cell, List.cons_append, List.nil_append, localsFrom]
  simp only [Nat.reduceAdd, Nat.reduceSub]
  rw [BitVec.add_zero, mTail,
      memRegion_zero (fsp + 0x10#64),
      memRegion_zero (fsp + 0x18#64),
      memRegion_zero (fsp + 0x20#64)]
  exact Entails.of_eq (by ac_rfl)

/-! ## 4. `.keepsFs` `memcpy` Call-Site Helper for `main` -/

private theorem memcpyCallee_fnOff :
    libsignalSessionCode.fnOff "memcpy" = num% (ls_off% "memcpy") :=
  ls_stub% "memcpy"

private theorem call_inImage {α : Type} {prog : Program} {img : Obj.Image}
    {callee retPc ret : BitVec 64} {spec : Spec α} {s0 s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (x : α)
    (hcall : subroutine_ok prog callee (spec.inImage img))
    (hinv : ImgCallInv img s)
    (hpc : s.pc = callee)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = retPc)
    (hP : P ⊢ spec.pre x s ∗ F)
    (hpanic : ∀ sf R', sf.status = .Panicked →
      (sf.mem ⊨ spec.onPanic x s sf ∗ R') → Qp sf (spec.onPanic x s sf ∗ F) := by
      intro _ _ _ hp; exact (not_satisfies_false_sepConj hp).elim)
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False := by
      intro _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ mainOom s0 sf ∗ R') := by
      intro _ _ _ ho; exact (not_satisfies_false_sepConj ho).elim)
    (hnext : ∀ sf : State,
      ImgCallInv img sf →
      sf.pc = retPc →
      sf.status = .Running →
      sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp (mainOom s0)) :
    SepWPp prog ret s P Q Qp (mainOom s0) := by
  exact ProofLib.SepWPp.call_wpp_frozen (x := x) (F := F) hcall hinv.1 hinv.2 hpc hrun hsp hlr
    (fun R hm => by
      have hm_pre : s.mem ⊨ (spec.pre x s ∗ F) ∗ R :=
        Satisfies.mono (sepConj_mono_left hP) hm
      dsimp only [Spec.inImage]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hinv, by simpa only [sepConj_assoc] using hm_pre⟩)
    (fun sf code R' hex hpost => hexit sf code R' hex hpost)
    (fun sf hpan ⟨R', hpost⟩ => hpanic sf R' hpan hpost)
    (fun sf hpcm hrunm hspm hcsm hfz hsym => hnext sf ⟨hfz, hsym⟩ hpcm hrunm hspm hcsm)
    (fun sf R' hoom_s hpost => hoom sf R' hoom_s hpost)

theorem main_sessionMemcpyRegionFs_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsFs img A ext) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr mainName + BitVec.ofNat 64 (ls_rel% "main" "memcpy"))
      ((withStack sessionMemcpyRegionSpec extHookStack).keepsFs.inImage img) :=
  hA.session_memcpy_region_ok_at mainName (ls_rel% "main" "memcpy")
    extHookStack (by decide) (by decide) (by rw [main_fnOff, memcpyCallee_fnOff])

/-- Step a `bl memcpy` call in `main` under `(withStack sessionMemcpyRegionSpec extHookStack).keepsFs`,
preserving `fs`, `trace`, `sp`, `CalleeSavedPreserved`, and `ImgCallInv`, and copying `src ↦ₛ bs`
into `memRegion dst bs.length`. -/
theorem step_memcpy_region_fs {prog : Program} {img : Obj.Image}
    {memcpyTarget fsp retPc ret dst src : BitVec 64} {bs : List (BitVec 8)}
    {fs0 : FsState} {tr0 : List TraceEvent}
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hmc : subroutine_ok prog memcpyTarget
      ((withStack sessionMemcpyRegionSpec extHookStack).keepsFs.inImage img))
    (hinv : ImgCallInv img s)
    (hpc : s.pc = memcpyTarget)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hal : s.spAligned = true)
    (hlr : s.readReg64 .lr = retPc)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hfs : s.fs = fs0)
    (htr : s.trace = tr0)
    (hP : P ⊢ memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt fsp extHookStack ∗ F)
    (hk : ∀ sm : State,
      ImgCallInv img sm →
      sm.pc = retPc →
      sm.status = .Running →
      sm.sp = fsp →
      CalleeSavedPreserved s sm →
      sm.fs = fs0 →
      sm.trace = tr0 →
      SepWPp prog ret sm
        (((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ stackAt fsp extHookStack ∗ F)
        Q Qp (mainOom s0)) :
    SepWPp prog ret s P Q Qp (mainOom s0) := by
  refine call_inImage (dst, src, bs) hmc hinv hpc hrun hal hlr
    (F := F)
    (hP := ?_)
    (hpanic := fun _ _ _ hp => by
      dsimp only [Spec.keepsFs, withStack, sessionMemcpyRegionSpec] at hp
      exact (not_satisfies_false_sepConj hp).elim)
    (hexit := fun _ _ _ _ he => by
      dsimp only [Spec.keepsFs, withStack, sessionMemcpyRegionSpec] at he
      exact not_satisfies_false_sepConj he)
    (hoom := fun _ _ _ ho => by
      dsimp only [Spec.keepsFs, withStack, sessionMemcpyRegionSpec] at ho
      exact (not_satisfies_false_sepConj ho).elim)
    (hnext := ?_)
  · dsimp only [Spec.keepsFs, withStack, sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [hsp]
    refine Entails.trans hP ?_
    have hpure :
        ⌜s.readReg64 .x0 = dst ∧ s.readReg64 .x1 = src ∧ (s.readReg64 .x2).toNat = bs.length⌝ =
        (emp : SepProp) := by
      simp [hx0, hx1, hx2]
    rw [hpure, emp_sepConj]
    exact Entails.of_eq (by ac_rfl)
  · intro sm hinv_m hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    dsimp only [Spec.keepsFs, withStack, sessionMemcpyRegionSpec]
    rw [hsp]
    have hpure_pull :
        ((⌜sm.fs = s.fs⌝ ∗
          (⌜sm.readReg64 .x0 = dst ∧ sm.trace = s.trace⌝ ∗ (dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗
          stackAt fsp extHookStack) ∗ F) =
        ⌜sm.fs = s.fs⌝ ∗
          (⌜sm.readReg64 .x0 = dst ∧ sm.trace = s.trace⌝ ∗
            (((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ stackAt fsp extHookStack ∗ F)) := by
      ac_rfl
    rw [hpure_pull]
    refine SepWPp.pure_elim fun hfsm => ?_
    refine SepWPp.pure_elim fun ⟨_, htrm⟩ => ?_
    exact hk sm hinv_m hpcm hrunm hspm hcsm (hfsm.trans hfs) (htrm.trans htr)

end M5MovesHelpers

end CryptoVerification.SignalSession.Cli.MainHops
