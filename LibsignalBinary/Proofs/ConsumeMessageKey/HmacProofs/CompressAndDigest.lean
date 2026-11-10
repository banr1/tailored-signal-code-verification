/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.EntryAndKeyBlock
public import LibsignalBinary.Proofs.ConsumeMessageKey.Defs
import GeneratedLean.LibsignalSession -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants

/-!
# Inner/Outer Compression and Digest Extraction of `crypto::hmac_sha256`

Symbolic execution of `hmac_sha256` from `0x20d0c` to `ret` (`0x20e8c`, Block 73): inner-block
padding and `compress256`, outer-block construction and `compress256`, stack zeroization, big-endian
digest write, and final assembly of `hmac_sha256_ok`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace CryptoVerification.LibsignalSession.CryptoHmacSha256

open Arm64 ProofLib CryptoGames CryptoGames.HMAC
open CryptoVerification.LibsignalAesCbc
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (shaStateBytes readShaState compress256Hook)
open CryptoVerification.RustHeap

attribute [local arm64_norm] Memory.read128 Memory.write128 MemWidth.bytes SimdMemSize.bytes

/-! ## Endianness and Digest Helpers -/

theorem shaState_toList_eq (st : ShaState) :
    st.toList = [st.get 0, st.get 1, st.get 2, st.get 3, st.get 4, st.get 5, st.get 6, st.get 7] := by
  rcases st with ⟨l, hl⟩
  rcases l with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨w7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try { simp at hl }
  rfl

private theorem toLEBytes_4_append_drop_take (w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 32) (i : Fin 8) :
    (((toLEBytes 4 w0 ++ toLEBytes 4 w1 ++ toLEBytes 4 w2 ++ toLEBytes 4 w3 ++
       toLEBytes 4 w4 ++ toLEBytes 4 w5 ++ toLEBytes 4 w6 ++ toLEBytes 4 w7).drop (4 * i.val)).take 4) =
      toLEBytes 4 ([w0, w1, w2, w3, w4, w5, w6, w7].get ⟨i.val, by simp⟩) := by
  fin_cases i <;> rfl

theorem read32_of_readBytes_shaStateBytes {m : Memory} {a : BitVec 64} {st : ShaState}
    (h : m.readBytes a 32 = shaStateBytes st) (i : Fin 8) :
    m.read32 (a + BitVec.ofNat 64 (4 * i.val)) = st.get i := by
  have hlen : (shaStateBytes st).length = 32 := shaStateBytes_length st
  have hslice := readBytes_slice_of_readBytes_eq m a (shaStateBytes st)
    (by rw [hlen, h]) (4 * i.val) 4 (by omega)
  have hflat : shaStateBytes st =
      toLEBytes 4 (st.get 0) ++ toLEBytes 4 (st.get 1) ++ toLEBytes 4 (st.get 2) ++ toLEBytes 4 (st.get 3) ++
      toLEBytes 4 (st.get 4) ++ toLEBytes 4 (st.get 5) ++ toLEBytes 4 (st.get 6) ++ toLEBytes 4 (st.get 7) := by
    unfold shaStateBytes
    rw [shaState_toList_eq st]
    simp [List.flatMap]
  rw [hflat, toLEBytes_4_append_drop_take] at hslice
  have hget : [st.get 0, st.get 1, st.get 2, st.get 3, st.get 4, st.get 5, st.get 6, st.get 7].get ⟨i.val, by simp⟩ =
      st.get i := by
    fin_cases i <;> rfl
  rw [hget] at hslice
  exact read32_of_readBytes_toLEBytes m _ _ hslice

theorem read32_writeBytes_shaStateBytes (m : Memory) (base off : BitVec 64) (st : ShaState)
    (i : Fin 8) :
    (m.writeBytes (base + off) (shaStateBytes st)).read32
      (base + (off + BitVec.ofNat 64 (4 * i.val))) = st.get i := by
  have hm : (m.writeBytes (base + off) (shaStateBytes st)).readBytes (base + off) 32 =
      shaStateBytes st := by
    simpa using ProofLib.readBytes_writeBytes_same m (base + off) (shaStateBytes st) (by simp)
  have hadd : base + (off + BitVec.ofNat 64 (4 * i.val)) =
      (base + off) + BitVec.ofNat 64 (4 * i.val) := by bv_omega
  rw [hadd]
  exact read32_of_readBytes_shaStateBytes hm i

theorem toBEBytes_4_eq_list {w : ℕ} (x : BitVec w) :
    toBEBytes 4 x =
      [x.extractLsb' 24 8, x.extractLsb' 16 8, x.extractLsb' 8 8, x.extractLsb' 0 8] :=
  rfl

theorem toBEBytes_8_eq_list {w : ℕ} (x : BitVec w) :
    toBEBytes 8 x =
      [x.extractLsb' 56 8, x.extractLsb' 48 8, x.extractLsb' 40 8, x.extractLsb' 32 8,
       x.extractLsb' 24 8, x.extractLsb' 16 8, x.extractLsb' 8 8, x.extractLsb' 0 8] :=
  rfl

private theorem toLEBytes_8_concat8 (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    toLEBytes 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) =
      [b0, b1, b2, b3, b4, b5, b6, b7] := by
  rw [toLEBytes_8_eq_list]
  simp only [List.cons.injEq, and_true]
  refine ⟨by bv_bits, by bv_bits, by bv_bits, by bv_bits,
          by bv_bits, by bv_bits, by bv_bits, by bv_bits⟩

private theorem truncate32_concat8 (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).truncate 32 =
      b3 ++ b2 ++ b1 ++ b0 := by
  bv_bits

private theorem toLEBytes_4_concat4 (b3 b2 b1 b0 : BitVec 8) :
    toLEBytes 4 (b3 ++ b2 ++ b1 ++ b0) = [b0, b1, b2, b3] := by
  rw [toLEBytes_4_eq_list]
  simp only [List.cons.injEq, and_true]
  refine ⟨by bv_bits, by bv_bits, by bv_bits, by bv_bits⟩

private theorem toLEBytes_8_concat44 (b3 b2 b1 b0 c3 c2 c1 c0 : BitVec 8) :
    toLEBytes 8 ((b3 ++ b2 ++ b1 ++ b0) ++ (c3 ++ c2 ++ c1 ++ c0)) =
      [c0, c1, c2, c3, b0, b1, b2, b3] := by
  rw [toLEBytes_8_eq_list]
  simp only [List.cons.injEq, and_true]
  refine ⟨by bv_bits, by bv_bits, by bv_bits, by bv_bits,
          by bv_bits, by bv_bits, by bv_bits, by bv_bits⟩

private theorem extractLsb'_zeroExtend64_32 (w : BitVec 32) :
    (w.zeroExtend 64).extractLsb' 0 8 = w.extractLsb' 0 8 ∧
    (w.zeroExtend 64).extractLsb' 8 8 = w.extractLsb' 8 8 ∧
    (w.zeroExtend 64).extractLsb' 16 8 = w.extractLsb' 16 8 ∧
    (w.zeroExtend 64).extractLsb' 24 8 = w.extractLsb' 24 8 := by
  refine ⟨by bv_bits, by bv_bits, by bv_bits, by bv_bits⟩

theorem toLEBytes_4_rev32_64 (w : BitVec 32) :
    toLEBytes 4 ((rev32_64 (w.zeroExtend 64)).truncate 32) = toBEBytes 4 w := by
  dsimp only [rev32_64]
  rw [truncate32_concat8, toLEBytes_4_concat4, toBEBytes_4_eq_list]
  have ⟨h0, h1, h2, h3⟩ := extractLsb'_zeroExtend64_32 w
  rw [h0, h1, h2, h3]

theorem toLEBytes_8_rev64 (x : BitVec 64) :
    toLEBytes 8 (rev64 x) = toBEBytes 8 x := by
  dsimp only [rev64]
  rw [toLEBytes_8_concat8, toBEBytes_8_eq_list]

theorem write32_rev32_64_eq_writeBytes (m : Memory) (a : BitVec 64) (w : BitVec 32) :
    m.write32 a ((rev32_64 (w.zeroExtend 64)).truncate 32) = m.writeBytes a (toBEBytes 4 w) := by
  rw [write32_eq_writeBytes, toLEBytes_4_rev32_64]

theorem digestBytes_eq_append (st : ShaState) :
    digestBytes st =
      toBEBytes 4 (st.get 0) ++ toBEBytes 4 (st.get 1) ++
      toBEBytes 4 (st.get 2) ++ toBEBytes 4 (st.get 3) ++
      toBEBytes 4 (st.get 4) ++ toBEBytes 4 (st.get 5) ++
      toBEBytes 4 (st.get 6) ++ toBEBytes 4 (st.get 7) := by
  unfold digestBytes
  rw [shaState_toList_eq st]
  simp [List.flatMap]

theorem write32_rev32_64_8_eq_writeBytes_digestBytes (m : Memory) (a : BitVec 64) (st : ShaState) :
    (((((((m.write32 a ((rev32_64 ((st.get 0).zeroExtend 64)).truncate 32)).write32
      (a + 4#64) ((rev32_64 ((st.get 1).zeroExtend 64)).truncate 32)).write32
      (a + 8#64) ((rev32_64 ((st.get 2).zeroExtend 64)).truncate 32)).write32
      (a + 12#64) ((rev32_64 ((st.get 3).zeroExtend 64)).truncate 32)).write32
      (a + 16#64) ((rev32_64 ((st.get 4).zeroExtend 64)).truncate 32)).write32
      (a + 20#64) ((rev32_64 ((st.get 5).zeroExtend 64)).truncate 32)).write32
      (a + 24#64) ((rev32_64 ((st.get 6).zeroExtend 64)).truncate 32)).write32
      (a + 28#64) ((rev32_64 ((st.get 7).zeroExtend 64)).truncate 32) =
      m.writeBytes a (digestBytes st) := by
  rw [digestBytes_eq_append st]
  simp only [write32_rev32_64_eq_writeBytes, writeBytes_append, toBEBytes_length,
    List.length_append]

theorem toLEBytes_8_rev32_append (x0 x1 : BitVec 32) :
    toLEBytes 8 ((rev32_64 (x1.zeroExtend 64)).truncate 32 ++
      (rev32_64 (x0.zeroExtend 64)).truncate 32) =
      toBEBytes 4 x0 ++ toBEBytes 4 x1 := by
  dsimp only [rev32_64]
  rw [truncate32_concat8, truncate32_concat8, toLEBytes_8_concat44,
      toBEBytes_4_eq_list, toBEBytes_4_eq_list]
  have ⟨a0, a1, a2, a3⟩ := extractLsb'_zeroExtend64_32 x0
  have ⟨b0, b1, b2, b3⟩ := extractLsb'_zeroExtend64_32 x1
  rw [a0, a1, a2, a3, b0, b1, b2, b3]
  rfl

theorem read64_writeBytes_shaStateBytes_off_disjoint (m : Memory) (base off1 off2 : BitVec 64)
    (st : ShaState)
    (hd : 8 ≤ (off1 - off2).toNat ∧ 32 ≤ (off2 - off1).toNat := by decide) :
    (m.writeBytes (base + off1) (shaStateBytes st)).read64 (base + off2) = m.read64 (base + off2) :=
  read64_writeBytes_off_disjoint m base off1 off2 (shaStateBytes st) (by simpa using hd)

theorem readBytes_writeBytes_shaStateBytes_off_disjoint (m : Memory) (base off1 off2 : BitVec 64)
    (n : ℕ) (st : ShaState)
    (hd : n ≤ (off1 - off2).toNat ∧ 32 ≤ (off2 - off1).toNat := by decide) :
    (m.writeBytes (base + off1) (shaStateBytes st)).readBytes (base + off2) n =
      m.readBytes (base + off2) n :=
  readBytes_writeBytes_off_disjoint m base off1 off2 n (shaStateBytes st) (by simpa using hd)

abbrev innerDigest (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (byte : BitVec 8) : ShaState :=
  F (innerState F key) (innerLastBlock [byte])

abbrev outerDigest (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (byte : BitVec 8) : ShaState :=
  F (outerState F key) (outerBlock (digestBytes (innerDigest F key byte)))

/-! ## Inner Block and First `compress256` (`0x20d0c → 0x20d74`) -/

structure StateH2c (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (byte : BitVec 8) (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% "sha2::sha256::compress256")
  common  : HmacCommon s₀ s
  x0_eq   : s.readReg64 .x0 = hsp s₀ + 208#64
  x1_eq   : s.readReg64 .x1 = hsp s₀ + 304#64
  x2_eq   : s.readReg64 .x2 = 1#64
  lr_eq   : s.readReg64 .lr = b + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" + 492)
  x19_eq  : s.readReg64 .x19 = s₀.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = hsp s₀ + 144#64
  x21_eq  : s.readReg64 .x21 = hsp s₀ + 208#64
  x22_eq  : s.readReg64 .x22 = hsp s₀ + 144#64
  x23_eq  : s.readReg64 .x23 = 128#64
  ist_eq  : s.mem.readBytes (hsp s₀ + 208#64) 32 = shaStateBytes (innerState F key)
  iblk_eq : s.mem.readBytes (hsp s₀ + 304#64) 64 = innerLastBlock [byte]
  ost_eq  : s.mem.readBytes (hsp s₀ + 248#64) 32 = shaStateBytes (outerState F key)
  obl_eq  : s.mem.read64 (hsp s₀ + 280#64) = 1#64

structure StateH3 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (byte : BitVec 8) (s₀ s : State) : Prop where
  pc_eq  : s.pc = b + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" + 492)
  common : HmacCommon s₀ s
  x19_eq : s.readReg64 .x19 = s₀.readReg64 .x0
  x20_eq : s.readReg64 .x20 = hsp s₀ + 144#64
  x21_eq : s.readReg64 .x21 = hsp s₀ + 208#64
  x22_eq : s.readReg64 .x22 = hsp s₀ + 144#64
  x23_eq : s.readReg64 .x23 = 128#64
  hi0    : s.mem.read32 (hsp s₀ + 208#64) = (innerDigest F key byte).get 0
  hi1    : s.mem.read32 (hsp s₀ + 212#64) = (innerDigest F key byte).get 1
  hi2    : s.mem.read32 (hsp s₀ + 216#64) = (innerDigest F key byte).get 2
  hi3    : s.mem.read32 (hsp s₀ + 220#64) = (innerDigest F key byte).get 3
  hi4    : s.mem.read32 (hsp s₀ + 224#64) = (innerDigest F key byte).get 4
  hi5    : s.mem.read32 (hsp s₀ + 228#64) = (innerDigest F key byte).get 5
  hi6    : s.mem.read32 (hsp s₀ + 232#64) = (innerDigest F key byte).get 6
  hi7    : s.mem.read32 (hsp s₀ + 236#64) = (innerDigest F key byte).get 7
  ost_eq : s.mem.readBytes (hsp s₀ + 248#64) 32 = shaStateBytes (outerState F key)
  obl_eq : s.mem.read64 (hsp s₀ + 280#64) = 1#64

open State (readReg64_setMem pc_setMem status_setMem sp_setMem)

private theorem pc_setMem_setPC (s : State) (m : Memory) (pc : BitVec 64) :
    ((s.setMem m).setPC pc).pc = pc := rfl

private theorem status_setMem_setPC (s : State) (m : Memory) (pc : BitVec 64) :
    ((s.setMem m).setPC pc).status = s.status := rfl

private theorem sp_setMem_setPC (s : State) (m : Memory) (pc : BitVec 64) :
    ((s.setMem m).setPC pc).sp = s.sp := rfl

private theorem readReg64_setMem_setPC (s : State) (m : Memory) (pc : BitVec 64) (r : Reg) :
    ((s.setMem m).setPC pc).readReg64 r = s.readReg64 r := rfl

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

theorem seg2a_runsTo {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {key : List (BitVec 8)} {byte : BitVec 8}
    {s₀ s : State}
    (hpre : HmacPre b F key [byte] s₀)
    (hs : StateH2 b F key byte s₀ s) :
    RunsTo (P b F alloc) s (StateH2c b F key byte s₀) := by
  generalize hPost : StateH2c b F key byte s₀ = Post
  rcases hs with ⟨hpc, ⟨hstat, hsp_eq, hx29, hx27, hsaved, hframe⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26,
    hm144, hm152, hm160, hm168, hm176, hm184, hm192,
    hist, hibl, host, hobl⟩
  have hal_hsp : (hsp s₀ &&& 0b1111#64) = 0#64 := hsp_align hpre.sp_aligned
  have hrw_hsp : s.mem.RW (hsp s₀) 480 :=
    ((hframe.rw_iff _ _).mpr hpre.rw_stack).sub (by unfold hsp; clear * -; bv_omega)
  iterate 14 sess_step
  subst hPost
  refine RunsTo.refl ?_
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [pc_setMem]; simp only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm]
  · rw [status_setMem]; simp only [arm64_norm, hstat]
  · rw [sp_setMem]; simp only [arm64_norm, hsp_eq]
  · rw [readReg64_setMem]; simp only [arm64_norm, hx29]
  · rw [readReg64_setMem]; simp only [arm64_norm, hx27]
  · rcases hsaved with ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩
    dsimp only [HmacSaved, State.setMem, State.writeReg64, State.writeReg32,
      State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm,
        s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11]
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32,
      State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    iterate 9 refine Frame.write64_stack1024 ?_ _ _
    exact hframe
  · rw [readReg64_setMem]; simp only [arm64_norm, hx21]
  · rw [readReg64_setMem]; simp only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm]
  · rw [readReg64_setMem]; simp only [arm64_norm]
  · rw [readReg64_setMem]; simp only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm]
  · rw [readReg64_setMem]; simp only [arm64_norm, hx19]
  · rw [readReg64_setMem]; simp only [arm64_norm, hx20]
  · rw [readReg64_setMem]; simp only [arm64_norm, hx21]
  · rw [readReg64_setMem]; simp only [arm64_norm, hx22]
  · rw [readReg64_setMem]; simp only [arm64_norm, hx23]
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32,
      State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    rw [readBytes_32_off_eq_read64]
    rw [readBytes_32_off_eq_read64] at hist
    simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm] at hist ⊢
    exact hist
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32,
      State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    rw [readBytes_64_off_eq_read64]
    simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm,
      hm144, hm152, hm160, hm168, hm176, hm184, hm192, toLEBytes_8_rev64]
    unfold innerLastBlock
    simp only [List.length_cons, List.length_nil]
    rfl
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32,
      State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    rw [readBytes_32_off_eq_read64]
    rw [readBytes_32_off_eq_read64] at host
    simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm] at host ⊢
    exact host
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32,
      State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm, hobl]

theorem seg2b_runsTo {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {key : List (BitVec 8)} {byte : BitVec 8}
    {s₀ s : State}
    (hpre : HmacPre b F key [byte] s₀)
    (hs : StateH2c b F key byte s₀ s) :
    RunsTo (P b F alloc) s (StateH3 b F key byte s₀) := by
  generalize hPost : StateH3 b F key byte s₀ = Post
  rcases hs with ⟨hpc, ⟨hstat, hsp_eq, hx29, hx27, hsaved, hframe⟩,
    hx0, hx1, hx2, hlr, hx19, hx20, hx21, hx22, hx23, hist, hiblk, host, hobl⟩
  have hrw_hsp : s.mem.RW (hsp s₀) 480 :=
    ((hframe.rw_iff _ _).mpr hpre.rw_stack).sub (by unfold hsp; clear * -; bv_omega)
  refine RunsTo.sess_compress256_step
    (stPtr := hsp s₀ + 208#64)
    (blkPtr := hsp s₀ + 304#64)
    (lr := b + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" + 492))
    (st := innerState F key)
    (blk := innerLastBlock [byte])
    (hrun := hstat)
    (hpc := hpc)
    (hx0 := hx0)
    (hx1 := hx1)
    (hx2 := hx2)
    (hlr := hlr)
    (hmem := rfl)
    (hst := hist)
    (hblk := hiblk)
    (hrw := hrw_hsp.sub (by clear * -; bv_omega))
    ?_
  subst hPost
  refine RunsTo.refl ?_
  refine ⟨pc_setMem_setPC _ _ _, ⟨(status_setMem_setPC _ _ _).trans hstat,
    (sp_setMem_setPC _ _ _).trans hsp_eq,
    (readReg64_setMem_setPC _ _ _ _).trans hx29,
    (readReg64_setMem_setPC _ _ _ _).trans hx27, ?_, ?_⟩,
    (readReg64_setMem_setPC _ _ _ _).trans hx19,
    (readReg64_setMem_setPC _ _ _ _).trans hx20,
    (readReg64_setMem_setPC _ _ _ _).trans hx21,
    (readReg64_setMem_setPC _ _ _ _).trans hx22,
    (readReg64_setMem_setPC _ _ _ _).trans hx23,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [State.setMem, State.setPC]
    exact hsaved.of_agreesOutside (AgreesOutside.writeBytes_self _ _ _)
      (by simp only [shaStateBytes_length, DisjointRegions]; clear * -; bv_omega)
  · dsimp only [State.setMem, State.setPC]
    exact Frame.writeBytes_stack1024 hframe _ _ (by simp only [shaStateBytes_length]; unfold hsp; clear * -; bv_omega)
  · dsimp only [State.setMem, State.setPC]
    exact read32_writeBytes_shaStateBytes s.mem (hsp s₀) 208#64 (innerDigest F key byte) 0
  · dsimp only [State.setMem, State.setPC]
    exact read32_writeBytes_shaStateBytes s.mem (hsp s₀) 208#64 (innerDigest F key byte) 1
  · dsimp only [State.setMem, State.setPC]
    exact read32_writeBytes_shaStateBytes s.mem (hsp s₀) 208#64 (innerDigest F key byte) 2
  · dsimp only [State.setMem, State.setPC]
    exact read32_writeBytes_shaStateBytes s.mem (hsp s₀) 208#64 (innerDigest F key byte) 3
  · dsimp only [State.setMem, State.setPC]
    exact read32_writeBytes_shaStateBytes s.mem (hsp s₀) 208#64 (innerDigest F key byte) 4
  · dsimp only [State.setMem, State.setPC]
    exact read32_writeBytes_shaStateBytes s.mem (hsp s₀) 208#64 (innerDigest F key byte) 5
  · dsimp only [State.setMem, State.setPC]
    exact read32_writeBytes_shaStateBytes s.mem (hsp s₀) 208#64 (innerDigest F key byte) 6
  · dsimp only [State.setMem, State.setPC]
    exact read32_writeBytes_shaStateBytes s.mem (hsp s₀) 208#64 (innerDigest F key byte) 7
  · dsimp only [State.setMem, State.setPC]
    rw [readBytes_writeBytes_shaStateBytes_off_disjoint s.mem (hsp s₀) 208#64 248#64 32]
    exact host
  · dsimp only [State.setMem, State.setPC]
    rw [read64_writeBytes_shaStateBytes_off_disjoint s.mem (hsp s₀) 208#64 280#64]
    exact hobl

theorem seg2_runsTo {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {key : List (BitVec 8)} {byte : BitVec 8}
    {s₀ s : State}
    (hpre : HmacPre b F key [byte] s₀)
    (hs : StateH2 b F key byte s₀ s) :
    RunsTo (P b F alloc) s (StateH3 b F key byte s₀) :=
  (seg2a_runsTo hpre hs).trans (fun _ h2c => seg2b_runsTo hpre h2c)

/-! ## Outer Block and Second `compress256` (`0x20d74 → 0x20df4`) -/

structure StateH3c (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (byte : BitVec 8) (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% "sha2::sha256::compress256")
  common  : HmacCommon s₀ s
  x0_eq   : s.readReg64 .x0 = hsp s₀ + 248#64
  x1_eq   : s.readReg64 .x1 = hsp s₀ + 304#64
  x2_eq   : s.readReg64 .x2 = 1#64
  lr_eq   : s.readReg64 .lr = b + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" + 620)
  x19_eq  : s.readReg64 .x19 = s₀.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = hsp s₀ + 144#64
  ost_eq  : s.mem.readBytes (hsp s₀ + 248#64) 32 = shaStateBytes (outerState F key)
  oblk_eq : s.mem.readBytes (hsp s₀ + 304#64) 64 = outerBlock (digestBytes (innerDigest F key byte))

structure StateH4 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (byte : BitVec 8) (s₀ s : State) : Prop where
  pc_eq  : s.pc = b + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" + 620)
  common : HmacCommon s₀ s
  x19_eq : s.readReg64 .x19 = s₀.readReg64 .x0
  x20_eq : s.readReg64 .x20 = hsp s₀ + 144#64
  ho0    : s.mem.read32 (hsp s₀ + 248#64) = (outerDigest F key byte).get 0
  ho1    : s.mem.read32 (hsp s₀ + 252#64) = (outerDigest F key byte).get 1
  ho2    : s.mem.read32 (hsp s₀ + 256#64) = (outerDigest F key byte).get 2
  ho3    : s.mem.read32 (hsp s₀ + 260#64) = (outerDigest F key byte).get 3
  ho4    : s.mem.read32 (hsp s₀ + 264#64) = (outerDigest F key byte).get 4
  ho5    : s.mem.read32 (hsp s₀ + 268#64) = (outerDigest F key byte).get 5
  ho6    : s.mem.read32 (hsp s₀ + 272#64) = (outerDigest F key byte).get 6
  ho7    : s.mem.read32 (hsp s₀ + 276#64) = (outerDigest F key byte).get 7

theorem Frame.write32_stack1024 {sp : BitVec 64} {m₀ m : Memory}
    (hf : Frame m₀ m [(sp - 1024#64, 1024)])
    (a : BitVec 64) (v : BitVec 32)
    (ha : (a - (sp - 1024#64)).toNat + 4 ≤ 1024 := by unfold hsp; clear * -; bv_omega) :
    Frame m₀ (m.write32 a v) [(sp - 1024#64, 1024)] := by
  rw [write32_eq_writeBytes]
  exact Frame.writeBytes_stack1024 hf a (toLEBytes 4 v) (by simpa using ha)

theorem seg3a_runsTo {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {key : List (BitVec 8)} {byte : BitVec 8}
    {s₀ s : State} (hpre : HmacPre b F key [byte] s₀) (hs : StateH3 b F key byte s₀ s) :
    RunsTo (P b F alloc) s (StateH3c b F key byte s₀) := by
  generalize hPost : StateH3c b F key byte s₀ = Post
  rcases hs with ⟨hpc, ⟨hstat, hsp_eq, hx29, hx27, hsaved, hframe⟩,
    hx19, hx20, hx21, hx22, hx23, hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, host, hobl⟩
  have hal_hsp : (hsp s₀ &&& 0b1111#64) = 0#64 := hsp_align hpre.sp_aligned
  have hrw_hsp : s.mem.RW (hsp s₀) 480 :=
    ((hframe.rw_iff _ _).mpr hpre.rw_stack).sub (by unfold hsp; clear * -; bv_omega)
  iterate 32 sess_step
  subst hPost; refine RunsTo.refl ?_
  refine ⟨by simp only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm],
    ⟨by simp only [arm64_norm, hstat], by simp only [arm64_norm, hsp_eq],
     by simp only [arm64_norm, hx29], by simp only [arm64_norm, hx27], ?_, ?_⟩,
    by simp only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm],
    by simp only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm],
    by simp only [arm64_norm], by simp only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm],
    by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20], ?_, ?_⟩
  · rcases hsaved with ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩
    dsimp only [HmacSaved, State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11]
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    iterate 10 refine Frame.write64_stack1024 ?_ _ _
    iterate 4 refine Frame.write32_stack1024 ?_ _ _
    refine Frame.write64_stack1024 ?_ _ _; iterate 4 refine Frame.write32_stack1024 ?_ _ _
    refine Frame.write64_stack1024 ?_ _ _; exact Frame.write8_stack1024 hframe _ _
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    rw [readBytes_32_off_eq_read64]; rw [readBytes_32_off_eq_read64] at host
    simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm] at host ⊢; exact host
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    rw [readBytes_64_off_eq_read64]
    simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm, hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hobl, toLEBytes_8_rev32_append, toLEBytes_8_rev64]
    rw [toLEBytes_8_read64_eq, toLEBytes_8_read64_eq, readBytes_8_eq, readBytes_8_eq]
    simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm]
    unfold outerBlock; rw [digestBytes_eq_append]
    simp only [List.append_assoc, List.cons_append, List.nil_append]; rfl

theorem seg3b_runsTo {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {key : List (BitVec 8)} {byte : BitVec 8}
    {s₀ s : State} (hpre : HmacPre b F key [byte] s₀) (hs : StateH3c b F key byte s₀ s) :
    RunsTo (P b F alloc) s (StateH4 b F key byte s₀) := by
  generalize hPost : StateH4 b F key byte s₀ = Post
  rcases hs with ⟨hpc, ⟨hstat, hsp_eq, hx29, hx27, hsaved, hframe⟩, hx0, hx1, hx2, hlr, hx19, hx20, host, hoblk⟩
  have hrw_hsp : s.mem.RW (hsp s₀) 480 := ((hframe.rw_iff _ _).mpr hpre.rw_stack).sub (by unfold hsp; clear * -; bv_omega)
  refine RunsTo.sess_compress256_step
    (stPtr := hsp s₀ + 248#64) (blkPtr := hsp s₀ + 304#64)
    (lr := b + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" + 620))
    (st := outerState F key) (blk := outerBlock (digestBytes (innerDigest F key byte)))
    (hrun := hstat) (hpc := hpc) (hx0 := hx0) (hx1 := hx1) (hx2 := hx2) (hlr := hlr)
    (hmem := rfl) (hst := host) (hblk := hoblk) (hrw := hrw_hsp.sub (by clear * -; bv_omega)) ?_
  subst hPost; refine RunsTo.refl ?_
  refine ⟨pc_setMem_setPC _ _ _, ⟨(status_setMem_setPC _ _ _).trans hstat,
    (sp_setMem_setPC _ _ _).trans hsp_eq, (readReg64_setMem_setPC _ _ _ _).trans hx29,
    (readReg64_setMem_setPC _ _ _ _).trans hx27, ?_, ?_⟩,
    (readReg64_setMem_setPC _ _ _ _).trans hx19, (readReg64_setMem_setPC _ _ _ _).trans hx20,
    read32_writeBytes_shaStateBytes s.mem (hsp s₀) 248#64 (outerDigest F key byte) 0,
    read32_writeBytes_shaStateBytes s.mem (hsp s₀) 248#64 (outerDigest F key byte) 1,
    read32_writeBytes_shaStateBytes s.mem (hsp s₀) 248#64 (outerDigest F key byte) 2,
    read32_writeBytes_shaStateBytes s.mem (hsp s₀) 248#64 (outerDigest F key byte) 3,
    read32_writeBytes_shaStateBytes s.mem (hsp s₀) 248#64 (outerDigest F key byte) 4,
    read32_writeBytes_shaStateBytes s.mem (hsp s₀) 248#64 (outerDigest F key byte) 5,
    read32_writeBytes_shaStateBytes s.mem (hsp s₀) 248#64 (outerDigest F key byte) 6,
    read32_writeBytes_shaStateBytes s.mem (hsp s₀) 248#64 (outerDigest F key byte) 7⟩
  · exact hsaved.of_agreesOutside (AgreesOutside.writeBytes_self _ _ _)
      (by simp only [shaStateBytes_length, DisjointRegions]; clear * -; bv_omega)
  · exact Frame.writeBytes_stack1024 hframe _ _ (by simp only [shaStateBytes_length]; unfold hsp; clear * -; bv_omega)

theorem seg3_runsTo {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {key : List (BitVec 8)} {byte : BitVec 8}
    {s₀ s : State} (hpre : HmacPre b F key [byte] s₀) (hs : StateH3 b F key byte s₀ s) :
    RunsTo (P b F alloc) s (StateH4 b F key byte s₀) :=
  (seg3a_runsTo hpre hs).trans (fun _ h3c => seg3b_runsTo hpre h3c)

/-! ## Stack Zeroization, Digest Write, and Return (`0x20df4 → 0x20e8c`) -/

@[local arm64_norm]
theorem read32_write8_base_off_disjoint (m : Memory) (base off1 off2 : BitVec 64) (v : BitVec 8)
    (hd : 4 ≤ (off1 - off2).toNat ∧ 1 ≤ (off2 - off1).toNat := by decide) :
    (m.write8 (base + off1) v).read32 (base + off2) = m.read32 (base + off2) :=
  (AgreesOutside.write8_self m (base + off1) v).read32_eq (by unfold DisjointRegions; clear * - hd; bv_omega)

theorem Frame.writeBytes_out {out sp : BitVec 64} {m₀ m : Memory}
    (hf : Frame m₀ m [(sp - 1024#64, 1024)])
    (bs : List (BitVec 8)) (hlen : bs.length = 32) :
    Frame m₀ (m.writeBytes out bs) [(out, 32), (sp - 1024#64, 1024)] := by
  have hag : AgreesOutside m (m.writeBytes out bs) out 32 :=
    hlen ▸ AgreesOutside.writeBytes_self m out bs
  exact hf.trans_agreesOutside hag

structure StateH4b (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (byte : BitVec 8) (s₀ s : State) : Prop where
  pc_eq  : s.pc = b + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" + 744)
  status : s.status = .Running
  sp_eq  : s.sp = hsp s₀
  x27_eq : s.readReg64 .x27 = s₀.readReg64 .x27
  saved  : HmacSaved s₀ (hsp s₀) s.mem
  out_eq : s.mem.readBytes (s₀.readReg64 .x0) 32 = hmacWith F key [byte]
  frame  : Frame s₀.mem s.mem [(s₀.readReg64 .x0, 32), (s₀.sp - 1024#64, 1024)]

theorem seg4a_runsTo {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {key : List (BitVec 8)} {byte : BitVec 8}
    {s₀ s : State}
    (hpre : HmacPre b F key [byte] s₀)
    (hs : StateH4 b F key byte s₀ s) :
    RunsTo (P b F alloc) s (StateH4b b F key byte s₀) := by
  generalize hPost : StateH4b b F key byte s₀ = Post
  rcases hs with ⟨hpc, ⟨hstat, hsp_eq, hx29, hx27, hsaved, hframe⟩,
    hx19, hx20, ho0, ho1, ho2, ho3, ho4, ho5, ho6, ho7⟩
  have hal_hsp : (hsp s₀ &&& 0b1111#64) = 0#64 := hsp_align hpre.sp_aligned
  have hrw_hsp : s.mem.RW (hsp s₀) 480 :=
    ((hframe.rw_iff _ _).mpr hpre.rw_stack).sub (by unfold hsp; clear * -; bv_omega)
  have hrw_out : s.mem.RW (s₀.readReg64 .x0) 32 :=
    (hframe.rw_iff _ _).mpr hpre.rw_out
  iterate 31 sess_step
  subst hPost
  refine RunsTo.refl ?_
  have hframe1 : Frame s₀.mem
      (((((((((((((((((s.mem.write8 (hsp s₀ + 207#64) 0#8).write64 (hsp s₀ + 304#64) 0#64).write64
        (hsp s₀ + 312#64) 0#64).write64 (hsp s₀ + 320#64) 0#64).write64 (hsp s₀ + 328#64) 0#64).write64
        (hsp s₀ + 336#64) 0#64).write64 (hsp s₀ + 344#64) 0#64).write64 (hsp s₀ + 352#64) 0#64).write64
        (hsp s₀ + 360#64) 0#64).write64 (hsp s₀ + 192#64) 0#64).write64 (hsp s₀ + 200#64) 0#64).write64
        (hsp s₀ + 176#64) 0#64).write64 (hsp s₀ + 184#64) 0#64).write64 (hsp s₀ + 160#64) 0#64).write64
        (hsp s₀ + 168#64) 0#64).write64 (hsp s₀ + 144#64) 0#64).write64 (hsp s₀ + 152#64) 0#64)
      [(s₀.sp - 1024#64, 1024)] := by
    iterate 16 refine Frame.write64_stack1024 ?_ _ _
    exact Frame.write8_stack1024 hframe _ _
  refine ⟨by simp only [hpc, BitVec.add_assoc, BitVec.reduceAdd, arm64_norm],
    by simp only [arm64_norm, hstat], by simp only [arm64_norm, hsp_eq],
    by simp only [arm64_norm, hx27], ?_, ?_, ?_⟩
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    rw [write32_rev32_64_8_eq_writeBytes_digestBytes]
    have hsaved1 : HmacSaved s₀ (hsp s₀)
        (((((((((((((((((s.mem.write8 (hsp s₀ + 207#64) 0#8).write64 (hsp s₀ + 304#64) 0#64).write64
          (hsp s₀ + 312#64) 0#64).write64 (hsp s₀ + 320#64) 0#64).write64 (hsp s₀ + 328#64) 0#64).write64
          (hsp s₀ + 336#64) 0#64).write64 (hsp s₀ + 344#64) 0#64).write64 (hsp s₀ + 352#64) 0#64).write64
          (hsp s₀ + 360#64) 0#64).write64 (hsp s₀ + 192#64) 0#64).write64 (hsp s₀ + 200#64) 0#64).write64
          (hsp s₀ + 176#64) 0#64).write64 (hsp s₀ + 184#64) 0#64).write64 (hsp s₀ + 160#64) 0#64).write64
          (hsp s₀ + 168#64) 0#64).write64 (hsp s₀ + 144#64) 0#64).write64 (hsp s₀ + 152#64) 0#64) := by
      rcases hsaved with ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩
      dsimp only [HmacSaved]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11]
    exact hsaved1.of_agreesOutside (AgreesOutside.writeBytes_self _ _ _) (by
      have hd := hpre.disj_out_stack
      simp only [digestBytes_length, DisjointRegions, Reg.x0] at hd ⊢; unfold hsp; clear * - hd; bv_omega)
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    rw [write32_rev32_64_8_eq_writeBytes_digestBytes]
    have hread : ∀ m : Memory,
        (m.writeBytes (s₀.readReg64 .x0) (digestBytes (outerDigest F key byte))).readBytes
          (s₀.readReg64 .x0) 32 = digestBytes (outerDigest F key byte) :=
      fun m => Layout.readBytes_writeBytes_eq m _ _ 32 (digestBytes_length _) (by decide)
    rw [hread, hmacWith_short F key [byte] (by rw [hpre.key_len]; decide) (by simp)]
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    rw [write32_rev32_64_8_eq_writeBytes_digestBytes]
    exact Frame.writeBytes_out hframe1 _ (digestBytes_length _)

structure StateH5 (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (byte : BitVec 8) (s₀ s : State) : Prop where
  pc_eq  : s.pc = s₀.readReg64 .lr
  status : s.status = .Running
  callee : CalleeSaved s₀ s
  out_eq : s.mem.readBytes (s₀.readReg64 .x0) 32 = hmacWith F key [byte]
  frame  : Frame s₀.mem s.mem [(s₀.readReg64 .x0, 32), (s₀.sp - 1024#64, 1024)]

theorem seg4b_runsTo {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {key : List (BitVec 8)} {byte : BitVec 8}
    {s₀ s : State} (hpre : HmacPre b F key [byte] s₀) (hs : StateH4b b F key byte s₀ s) :
    RunsTo (P b F alloc) s (StateH5 F key byte s₀) := by
  generalize hPost : StateH5 F key byte s₀ = Post
  rcases hs with ⟨hpc, hstat, hsp_eq, hx27, hsaved, hout, hframe⟩
  rcases hsaved with ⟨s29, slr, s28, s26, s25, s24, s23, s22, s21, s20, s19⟩
  have hal_hsp : (hsp s₀ &&& 0b1111#64) = 0#64 := hsp_align hpre.sp_aligned
  have hrw_hsp : s.mem.RW (hsp s₀) 480 :=
    ((hframe.rw_iff _ _).mpr hpre.rw_stack).sub (by unfold hsp; clear * -; bv_omega)
  iterate 8 sess_step
  subst hPost; refine RunsTo.refl ?_
  refine ⟨by simp only [arm64_norm, slr], by simp only [arm64_norm, hstat], ?_, hout, hframe⟩
  refine ⟨by simp only [arm64_norm, hsp_eq, ← hsp_eq_add], fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [arm64_norm, s19, s20, s21, s22, s23, s24, s25, s26, hx27, s28, s29, slr]

theorem seg4_runsTo {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {key : List (BitVec 8)} {byte : BitVec 8}
    {s₀ s : State} (hpre : HmacPre b F key [byte] s₀) (hs : StateH4 b F key byte s₀ s) :
    RunsTo (P b F alloc) s (StateH5 F key byte s₀) :=
  (seg4a_runsTo hpre hs).trans (fun _ h4b => seg4b_runsTo hpre h4b)

theorem hmac_runsTo {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {key : List (BitVec 8)} {byte : BitVec 8}
    {s₀ : State}
    (hpre : HmacPre b F key [byte] s₀) :
    RunsTo (P b F alloc) s₀ (StateH5 F key byte s₀) :=
  (seg0_runsTo hpre).trans fun _ h1 =>
  (seg1a_runsTo hpre h1).trans fun _ h1m =>
  (seg1b_runsTo hpre h1m).trans fun _ h2 =>
  (seg2_runsTo hpre h2).trans fun _ h3 =>
  (seg3_runsTo hpre h3).trans fun _ h4 =>
  seg4_runsTo hpre h4

/-! ## Bridge from `hmac_runsTo` to `HmacOk` -/

noncomputable abbrev roSecSlice : List (BitVec 8) :=
  (libsignalSessionImage.data.drop (num% (ls_str% "kyber_pre_key_pu") - num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)))).take 288

set_option maxRecDepth 2000000 in
open ProofLib.ProgramReflection in
theorem roSecSlice_length : roSecSlice.length = 288 := by
  rfl_kernel

set_option maxRecDepth 2000000 in
open ProofLib.ProgramReflection in
theorem rodata_sha256IV_bytes :
    (roSecSlice.drop 256).take 32 = shaStateBytes sha256IV := by
  rfl_kernel

open ProofLib.ProgramReflection in
theorem rodata_sha256IV {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} (hro : img.RoDataLoaded m) :
    m.RO (img.base + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 ∧
    m.readBytes (img.base + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 = shaStateBytes sha256IV := by
  have hdlen : num% (ls_str% "kyber_pre_key_pu") - num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)) + 288 ≤ libsignalSessionImage.data.length := by
    have hlen := roSecSlice_length
    simp only [roSecSlice, List.length_take, List.length_drop] at hlen
    omega
  have h := ProofLib.rodata_readBytes_disjoint himg (dataOff := num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44))) rfl
    (secOff := num% (ls_str% "kyber_pre_key_pu")) (secLen := 288) (by decide) (by decide) (by decide) hdlen (by rfl_kernel)
    m hro
  have hadd : img.base + bv% (ls_str% "kyber_pre_key_pu") + 256#64 = img.base + bv% (ls_str% "kyber_pre_key_pu" + 256) := by clear * -; bv_omega
  have hro32 : m.RO (img.base + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 := by
    intro a ha
    apply h.1 a
    unfold InRegion at ha ⊢
    clear * - ha; bv_omega
  have hslice := readBytes_slice_of_readBytes_eq m (img.base + bv% (ls_str% "kyber_pre_key_pu")) roSecSlice
    (by rw [roSecSlice_length]; exact h.2) 256 32 (by rw [roSecSlice_length])
  rw [hadd, rodata_sha256IV_bytes] at hslice
  exact ⟨hro32, hslice⟩

theorem disjointRegions_of_ro_rw {m : Memory} {b₁ b₂ : BitVec 64} {n₁ n₂ : Nat}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hro : m.RO b₁ n₁) (hrw : m.RW b₂ n₂) :
    DisjointRegions b₁ n₁ b₂ n₂ := by
  have hdisj : ∀ a, ¬ (InRegion b₁ n₁ a ∧ InRegion b₂ n₂ a) := by
    intro a ⟨h1, h2⟩
    have hp1 := (hro a h1).1
    have hp2 := (Memory.permNoLazy_eq_some_rw_iff.mp (hrw a h2)).1
    rw [hp1] at hp2; cases hp2
  constructor
  · apply Classical.byContradiction; intro hlt
    exact hdisj b₂ ⟨by simp only [InRegion]; omega,
      by simp only [InRegion, BitVec.sub_self, BitVec.toNat_zero]; omega⟩
  · apply Classical.byContradiction; intro hlt
    exact hdisj b₁ ⟨by simp only [InRegion, BitVec.sub_self, BitVec.toNat_zero]; omega,
      by simp only [InRegion]; omega⟩

theorem CallingConventionPreserved_of_calleeSaved {s₀ sf : State} (h : CalleeSaved s₀ sf)
    (hvregs : calleeSavedVRegs sf = calleeSavedVRegs s₀) :
    CallingConventionPreserved s₀ sf := by
  rcases h with ⟨hsp_eq, hregs⟩
  refine ⟨hsp_eq,
    hregs .x19 (by simp), hregs .x20 (by simp), hregs .x21 (by simp),
    hregs .x22 (by simp), hregs .x23 (by simp), hregs .x24 (by simp),
    hregs .x25 (by simp), hregs .x26 (by simp), hregs .x27 (by simp),
    hregs .x28 (by simp), hregs .x29 (by simp), hvregs⟩

theorem Frame.update_two_blocks {P1 P1' P2 P2' R : SepProp}
    {b1 b2 : BitVec 64} {n1 n2 : Nat} {Φ1 Φ1' Φ2 Φ2' : Memory → Prop}
    {m0 mf : Memory}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb1' : IsBlock P1' b1 n1 Φ1')
    (hb2 : IsBlock P2 b2 n2 Φ2) (hb2' : IsBlock P2' b2 n2 Φ2')
    (h0 : m0 ⊨ P1 ∗ (P2 ∗ R))
    (hf : Frame m0 mf [(b1, n1), (b2, n2)])
    (hΦ1' : Φ1' mf) (hΦ2' : Φ2' mf) :
    mf ⊨ P1' ∗ (P2' ∗ R) := by
  let m_mid : Memory := Memory.splice m0 mf b2 n2
  have hag1 : AgreesOutside m0 m_mid b2 n2 := hf.splice_agreesOutside_left
  have hag2 : AgreesOutside m_mid mf b1 n1 := hf.splice_agreesOutside_two
  have h0' : m0 ⊨ P2 ∗ (P1 ∗ R) := by
    rw [sepConj_left_comm]; exact h0
  have hmid' : m_mid ⊨ P2' ∗ (P1 ∗ R) :=
    hb2.update hb2' (Nat.le_refl _) h0' hag1
      (hb2'.congr mf m_mid (fun a ha => by simp [m_mid, ha]) hΦ2')
  have hmid : m_mid ⊨ P1 ∗ (P2' ∗ R) := by
    rw [sepConj_left_comm]; exact hmid'
  exact hb1.update hb1' (Nat.le_refl _) hmid hag2 hΦ1'

theorem hmac_sha256_ok' (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (alloc : String → Option (State → State)) (himg : Obj.Loads libsignalSessionImage img) :
    HmacOk img F alloc := by
  unfold HmacOk
  rw [sessionProg_eq_P himg F alloc]
  refine subroutine_ok_intro fun ⟨out, ka, key, ia, inp⟩ R s0 hpc hrun hpre hsp => ?_
  rw [Spec.inImage, hmacSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, _⟩, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2_nat, hx3, hx4_nat, hkey_len, hinp_len⟩, hsep⟩
  rcases inp with _ | ⟨byte, _ | _⟩ <;> try { simp at hinp_len }
  have hx2 : s0.readReg64 .x2 = 32#64 := by
    apply BitVec.eq_of_toNat_eq; simp [hx2_nat, hkey_len]
  have hx4 : s0.readReg64 .x4 = 1#64 := by
    apply BitVec.eq_of_toNat_eq; simp at hx4_nat; simp [hx4_nat]
  have hsp_split : stackAt s0.sp 2048 = memRegion (s0.sp - 2048#64) 1024 ∗ memRegion (s0.sp - 1024#64) 1024 :=
    stackAt_split_bottom s0.sp 1024 1024 (by decide)
  rw [hsp_split] at hsep
  have hb_out := IsBlock.memRegion out 32
  have hb_key := IsBlock.pointsToBytes_len (a := ka) hkey_len
  have hb_inp := IsBlock.pointsToBytes_len (a := ia) (rfl : [byte].length = 1)
  have hb_stk := IsBlock.memRegion (s0.sp - 1024#64) 1024
  have hsep_key : s0.mem ⊨ (ka ↦ₛ key) ∗ (memRegion (s0.sp - 1024#64) 1024 ∗
      (memRegion out 32 ∗ (ia ↦ₛ [byte]) ∗ memRegion (s0.sp - 2048#64) 1024 ∗ R)) := by
    ac_nf at hsep ⊢
  have hsep_inp : s0.mem ⊨ (ia ↦ₛ [byte]) ∗ (memRegion (s0.sp - 1024#64) 1024 ∗
      (memRegion out 32 ∗ (ka ↦ₛ key) ∗ memRegion (s0.sp - 2048#64) 1024 ∗ R)) := by
    ac_nf at hsep ⊢
  have hsep_out : s0.mem ⊨ memRegion out 32 ∗ (memRegion (s0.sp - 1024#64) 1024 ∗
      ((ka ↦ₛ key) ∗ (ia ↦ₛ [byte]) ∗ memRegion (s0.sp - 2048#64) 1024 ∗ R)) := by
    ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (s0.sp - 1024#64) 1024 ∗
      (memRegion out 32 ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ [byte]) ∗ memRegion (s0.sp - 2048#64) 1024 ∗ R) := by
    ac_nf at hsep ⊢
  have hkey_eq : s0.mem.readBytes ka 32 = key := by
    have h := (hb_key.read hsep_key).2
    rwa [hkey_len] at h
  have hinp_eq : s0.mem.readBytes ia 1 = [byte] :=
    (hb_inp.read hsep_inp).2
  have hrw_out : RW s0.mem out 32 :=
    fun a ha => hb_out.permNoLazy_rw hsep_out ha
  have hrw_stk : RW s0.mem (s0.sp - 1024#64) 1024 :=
    fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  have hread_inp : s0.mem.Readable ia 1 :=
    Memory.RW.readable (fun a ha => hb_inp.permNoLazy_rw hsep_inp ha)
  obtain ⟨hro_iv, hiv_eq⟩ := rodata_sha256IV himg hF.roData
  have hread_iv : s0.mem.Readable (img.base + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 :=
    fun a ha => ⟨by rw [(hro_iv a ha).1]; rfl, (hro_iv a ha).2⟩
  have hpre_hmac : HmacPre img.base F key [byte] s0 := {
    pc_eq := hpc
    status := hrun
    sp_aligned := by simpa [State.spAligned] using hsp
    base_aligned := ProofLib.base_aligned_of_loads himg
    x2_eq := hx2
    x4_eq := hx4
    key_len := hkey_len
    inp_len := rfl
    key_eq := by rw [hx1]; exact hkey_eq
    inp_eq := by rw [hx3]; exact hinp_eq
    iv_eq := hiv_eq
    read_iv := hread_iv
    read_inp := by rw [hx3]; exact hread_inp
    rw_out := by rw [hx0]; exact hrw_out
    rw_stack := hrw_stk
    disj_iv_stack := disjointRegions_of_ro_rw (by decide) (by decide) hro_iv hrw_stk
    disj_out_stack := by rw [hx0]; exact hb_out.disjoint hb_stk (by decide) (by decide) hsep_out
    disj_key_stack := by rw [hx1]; exact hb_key.disjoint hb_stk (by decide) (by decide) hsep_key
    disj_inp_stack := by rw [hx3]; exact hb_inp.disjoint hb_stk (by simp) (by decide) hsep_inp
  }
  refine (hmac_runsTo hpre_hmac).to_reaches_pc fun sf h5 hkf hsym htr hvregs => ?_
  rcases h5 with ⟨hpc_sf, hstat_sf, hcallee, hout_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee hvregs⟩
  rw [Spec.inImage, hmacSpec]
  dsimp only []
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr, ?_⟩
  rw [hsp_split]
  have hb_out' := IsBlock.pointsToBytes_len (a := out) (length_hmacWith F key [byte])
  rw [hx0] at hout_sf hframe_sf
  have hpost_sep : sf.mem ⊨ (out ↦ₛ hmacWith F key [byte]) ∗ (memRegion (s0.sp - 1024#64) 1024 ∗
      ((ka ↦ₛ key) ∗ (ia ↦ₛ [byte]) ∗ memRegion (s0.sp - 2048#64) 1024 ∗ R)) :=
    Frame.update_two_blocks hb_out hb_out' hb_stk hb_stk hsep_out hframe_sf
      ⟨by rw [length_hmacWith]; decide, by rwa [length_hmacWith]⟩ trivial
  ac_nf at hpost_sep ⊢

/-! ## Relocatable `[LibsignalPlacement]` Execution (Block 73) -/

structure StateH2cPlaced [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (byte : BitVec 8) (s₀ s : State) : Prop where
  pc_eq   : s.pc = lsρ lsCompress256Sym
  common  : HmacCommon s₀ s
  x0_eq   : s.readReg64 .x0 = hsp s₀ + 208#64
  x1_eq   : s.readReg64 .x1 = hsp s₀ + 304#64
  x2_eq   : s.readReg64 .x2 = 1#64
  lr_eq   : s.readReg64 .lr = (blkPl_73).base + 492#64
  x19_eq  : s.readReg64 .x19 = s₀.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = hsp s₀ + 144#64
  x21_eq  : s.readReg64 .x21 = hsp s₀ + 208#64
  x22_eq  : s.readReg64 .x22 = hsp s₀ + 144#64
  x23_eq  : s.readReg64 .x23 = 128#64
  ist_eq  : s.mem.readBytes (hsp s₀ + 208#64) 32 = shaStateBytes (innerState F key)
  iblk_eq : s.mem.readBytes (hsp s₀ + 304#64) 64 = innerLastBlock [byte]
  ost_eq  : s.mem.readBytes (hsp s₀ + 248#64) 32 = shaStateBytes (outerState F key)
  obl_eq  : s.mem.read64 (hsp s₀ + 280#64) = 1#64

structure StateH3Placed [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (byte : BitVec 8) (s₀ s : State) : Prop where
  pc_eq  : s.pc = (blkPl_73).base + 492#64
  common : HmacCommon s₀ s
  x19_eq : s.readReg64 .x19 = s₀.readReg64 .x0
  x20_eq : s.readReg64 .x20 = hsp s₀ + 144#64
  x21_eq : s.readReg64 .x21 = hsp s₀ + 208#64
  x22_eq : s.readReg64 .x22 = hsp s₀ + 144#64
  x23_eq : s.readReg64 .x23 = 128#64
  hi0    : s.mem.read32 (hsp s₀ + 208#64) = (innerDigest F key byte).get 0
  hi1    : s.mem.read32 (hsp s₀ + 212#64) = (innerDigest F key byte).get 1
  hi2    : s.mem.read32 (hsp s₀ + 216#64) = (innerDigest F key byte).get 2
  hi3    : s.mem.read32 (hsp s₀ + 220#64) = (innerDigest F key byte).get 3
  hi4    : s.mem.read32 (hsp s₀ + 224#64) = (innerDigest F key byte).get 4
  hi5    : s.mem.read32 (hsp s₀ + 228#64) = (innerDigest F key byte).get 5
  hi6    : s.mem.read32 (hsp s₀ + 232#64) = (innerDigest F key byte).get 6
  hi7    : s.mem.read32 (hsp s₀ + 236#64) = (innerDigest F key byte).get 7
  ost_eq : s.mem.readBytes (hsp s₀ + 248#64) 32 = shaStateBytes (outerState F key)
  obl_eq : s.mem.read64 (hsp s₀ + 280#64) = 1#64

theorem seg2a_placed_runsTo [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} {key : List (BitVec 8)} {byte : BitVec 8} {s₀ s : State}
    (hpre : HmacPlacedPre F key [byte] s₀) (hs : StateH2Placed F key byte s₀ s) :
    RunsTo (lsProg_73 H) s (StateH2cPlaced F key byte s₀) := by
  generalize hPost : StateH2cPlaced F key byte s₀ = Post
  rcases hs with ⟨hpc, ⟨hstat, hsp_eq, hx29, hx27, hsaved, hframe⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26,
    hm144, hm152, hm160, hm168, hm176, hm184, hm192, hist, hibl, host, hobl⟩
  have hal_hsp : (hsp s₀ &&& 0b1111#64) = 0#64 := hsp_align hpre.sp_aligned
  have hrw_hsp : s.mem.RW (hsp s₀) 480 :=
    ((hframe.rw_iff _ _).mpr hpre.rw_stack).sub (by unfold hsp; clear * -; bv_omega)
  iterate 14 sess_step
  subst hPost; refine RunsTo.refl ?_
  refine ⟨by rw [pc_setMem]; simp only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm, lsCompress256Sym],
    ⟨by rw [status_setMem]; simp only [arm64_norm, hstat],
     by rw [sp_setMem]; simp only [arm64_norm, hsp_eq],
     by rw [readReg64_setMem]; simp only [arm64_norm, hx29],
     by rw [readReg64_setMem]; simp only [arm64_norm, hx27], ?_, ?_⟩,
    by rw [readReg64_setMem]; simp only [arm64_norm, hx21],
    by rw [readReg64_setMem]; simp only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm],
    by rw [readReg64_setMem]; simp only [arm64_norm],
    by rw [readReg64_setMem]; simp only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm],
    by rw [readReg64_setMem]; simp only [arm64_norm, hx19],
    by rw [readReg64_setMem]; simp only [arm64_norm, hx20],
    by rw [readReg64_setMem]; simp only [arm64_norm, hx21],
    by rw [readReg64_setMem]; simp only [arm64_norm, hx22],
    by rw [readReg64_setMem]; simp only [arm64_norm, hx23], ?_, ?_, ?_, ?_⟩
  · rcases hsaved with ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩
    dsimp only [HmacSaved, State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11]
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    iterate 9 refine Frame.write64_stack1024 ?_ _ _
    exact hframe
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    rw [readBytes_32_off_eq_read64]; rw [readBytes_32_off_eq_read64] at hist
    simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm] at hist ⊢; exact hist
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    rw [readBytes_64_off_eq_read64]
    simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm, hm144, hm152, hm160, hm168, hm176, hm184, hm192, toLEBytes_8_rev64]
    unfold innerLastBlock; simp only [List.length_cons, List.length_nil]; rfl
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    rw [readBytes_32_off_eq_read64]; rw [readBytes_32_off_eq_read64] at host
    simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm] at host ⊢; exact host
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm, hobl]

theorem seg2b_placed_runsTo [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_compress : H lsCompress256Sym = some (compress256Hook F))
    {key : List (BitVec 8)} {byte : BitVec 8} {s₀ s : State}
    (hpre : HmacPlacedPre F key [byte] s₀) (hs : StateH2cPlaced F key byte s₀ s) :
    RunsTo (lsProg_73 H) s (StateH3Placed F key byte s₀) := by
  generalize hPost : StateH3Placed F key byte s₀ = Post
  rcases hs with ⟨hpc, ⟨hstat, hsp_eq, hx29, hx27, hsaved, hframe⟩,
    hx0, hx1, hx2, hlr, hx19, hx20, hx21, hx22, hx23, hist, hiblk, host, hobl⟩
  have hrw_hsp : s.mem.RW (hsp s₀) 480 :=
    ((hframe.rw_iff _ _).mpr hpre.rw_stack).sub (by unfold hsp; clear * -; bv_omega)
  refine RunsTo.placed_compress256_step h_compress
    (stPtr := hsp s₀ + 208#64) (blkPtr := hsp s₀ + 304#64) (lr := (blkPl_73).base + 492#64)
    (st := innerState F key) (blk := innerLastBlock [byte])
    (hrun := hstat) (hpc := hpc) (hx0 := hx0) (hx1 := hx1) (hx2 := hx2) (hlr := hlr)
    (hmem := rfl) (hst := hist) (hblk := hiblk) (hrw := hrw_hsp.sub (by clear * -; bv_omega)) ?_
  subst hPost; refine RunsTo.refl ?_
  refine ⟨pc_setMem_setPC _ _ _, ⟨(status_setMem_setPC _ _ _).trans hstat,
    (sp_setMem_setPC _ _ _).trans hsp_eq, (readReg64_setMem_setPC _ _ _ _).trans hx29,
    (readReg64_setMem_setPC _ _ _ _).trans hx27, ?_, ?_⟩,
    (readReg64_setMem_setPC _ _ _ _).trans hx19, (readReg64_setMem_setPC _ _ _ _).trans hx20,
    (readReg64_setMem_setPC _ _ _ _).trans hx21, (readReg64_setMem_setPC _ _ _ _).trans hx22,
    (readReg64_setMem_setPC _ _ _ _).trans hx23,
    read32_writeBytes_shaStateBytes s.mem (hsp s₀) 208#64 (innerDigest F key byte) 0,
    read32_writeBytes_shaStateBytes s.mem (hsp s₀) 208#64 (innerDigest F key byte) 1,
    read32_writeBytes_shaStateBytes s.mem (hsp s₀) 208#64 (innerDigest F key byte) 2,
    read32_writeBytes_shaStateBytes s.mem (hsp s₀) 208#64 (innerDigest F key byte) 3,
    read32_writeBytes_shaStateBytes s.mem (hsp s₀) 208#64 (innerDigest F key byte) 4,
    read32_writeBytes_shaStateBytes s.mem (hsp s₀) 208#64 (innerDigest F key byte) 5,
    read32_writeBytes_shaStateBytes s.mem (hsp s₀) 208#64 (innerDigest F key byte) 6,
    read32_writeBytes_shaStateBytes s.mem (hsp s₀) 208#64 (innerDigest F key byte) 7, ?_, ?_⟩
  · exact hsaved.of_agreesOutside (AgreesOutside.writeBytes_self _ _ _)
      (by simp only [shaStateBytes_length, DisjointRegions]; clear * -; bv_omega)
  · exact Frame.writeBytes_stack1024 hframe _ _ (by simp only [shaStateBytes_length]; unfold hsp; clear * -; bv_omega)
  · dsimp only [State.setMem, State.setPC]; rw [readBytes_writeBytes_shaStateBytes_off_disjoint s.mem (hsp s₀) 208#64 248#64 32]; exact host
  · dsimp only [State.setMem, State.setPC]; rw [read64_writeBytes_shaStateBytes_off_disjoint s.mem (hsp s₀) 208#64 280#64]; exact hobl

theorem seg2_placed_runsTo [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_compress : H lsCompress256Sym = some (compress256Hook F))
    {key : List (BitVec 8)} {byte : BitVec 8} {s₀ s : State}
    (hpre : HmacPlacedPre F key [byte] s₀) (hs : StateH2Placed F key byte s₀ s) :
    RunsTo (lsProg_73 H) s (StateH3Placed F key byte s₀) :=
  (seg2a_placed_runsTo hpre hs).trans (fun _ h2c => seg2b_placed_runsTo h_compress hpre h2c)

structure StateH3cPlaced [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (byte : BitVec 8) (s₀ s : State) : Prop where
  pc_eq   : s.pc = lsρ lsCompress256Sym
  common  : HmacCommon s₀ s
  x0_eq   : s.readReg64 .x0 = hsp s₀ + 248#64
  x1_eq   : s.readReg64 .x1 = hsp s₀ + 304#64
  x2_eq   : s.readReg64 .x2 = 1#64
  lr_eq   : s.readReg64 .lr = (blkPl_73).base + 620#64
  x19_eq  : s.readReg64 .x19 = s₀.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = hsp s₀ + 144#64
  ost_eq  : s.mem.readBytes (hsp s₀ + 248#64) 32 = shaStateBytes (outerState F key)
  oblk_eq : s.mem.readBytes (hsp s₀ + 304#64) 64 = outerBlock (digestBytes (innerDigest F key byte))

structure StateH4Placed [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (byte : BitVec 8) (s₀ s : State) : Prop where
  pc_eq  : s.pc = (blkPl_73).base + 620#64
  common : HmacCommon s₀ s
  x19_eq : s.readReg64 .x19 = s₀.readReg64 .x0
  x20_eq : s.readReg64 .x20 = hsp s₀ + 144#64
  ho0    : s.mem.read32 (hsp s₀ + 248#64) = (outerDigest F key byte).get 0
  ho1    : s.mem.read32 (hsp s₀ + 252#64) = (outerDigest F key byte).get 1
  ho2    : s.mem.read32 (hsp s₀ + 256#64) = (outerDigest F key byte).get 2
  ho3    : s.mem.read32 (hsp s₀ + 260#64) = (outerDigest F key byte).get 3
  ho4    : s.mem.read32 (hsp s₀ + 264#64) = (outerDigest F key byte).get 4
  ho5    : s.mem.read32 (hsp s₀ + 268#64) = (outerDigest F key byte).get 5
  ho6    : s.mem.read32 (hsp s₀ + 272#64) = (outerDigest F key byte).get 6
  ho7    : s.mem.read32 (hsp s₀ + 276#64) = (outerDigest F key byte).get 7

theorem seg3a_placed_runsTo [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} {key : List (BitVec 8)} {byte : BitVec 8} {s₀ s : State}
    (hpre : HmacPlacedPre F key [byte] s₀) (hs : StateH3Placed F key byte s₀ s) :
    RunsTo (lsProg_73 H) s (StateH3cPlaced F key byte s₀) := by
  generalize hPost : StateH3cPlaced F key byte s₀ = Post
  rcases hs with ⟨hpc, ⟨hstat, hsp_eq, hx29, hx27, hsaved, hframe⟩,
    hx19, hx20, hx21, hx22, hx23, hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, host, hobl⟩
  have hal_hsp : (hsp s₀ &&& 0b1111#64) = 0#64 := hsp_align hpre.sp_aligned
  have hrw_hsp : s.mem.RW (hsp s₀) 480 :=
    ((hframe.rw_iff _ _).mpr hpre.rw_stack).sub (by unfold hsp; clear * -; bv_omega)
  iterate 32 sess_step
  subst hPost; refine RunsTo.refl ?_
  refine ⟨by simp only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm, lsCompress256Sym],
    ⟨by simp only [arm64_norm, hstat], by simp only [arm64_norm, hsp_eq],
     by simp only [arm64_norm, hx29], by simp only [arm64_norm, hx27], ?_, ?_⟩,
    by simp only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm],
    by simp only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm],
    by simp only [arm64_norm], by simp only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm],
    by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20], ?_, ?_⟩
  · rcases hsaved with ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩
    dsimp only [HmacSaved, State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11]
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    iterate 10 refine Frame.write64_stack1024 ?_ _ _
    iterate 4 refine Frame.write32_stack1024 ?_ _ _
    refine Frame.write64_stack1024 ?_ _ _; iterate 4 refine Frame.write32_stack1024 ?_ _ _
    refine Frame.write64_stack1024 ?_ _ _; exact Frame.write8_stack1024 hframe _ _
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    rw [readBytes_32_off_eq_read64]; rw [readBytes_32_off_eq_read64] at host
    simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm] at host ⊢; exact host
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    rw [readBytes_64_off_eq_read64]
    simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm, hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hobl, toLEBytes_8_rev32_append, toLEBytes_8_rev64]
    rw [toLEBytes_8_read64_eq, toLEBytes_8_read64_eq, readBytes_8_eq, readBytes_8_eq]
    simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm]
    unfold outerBlock; rw [digestBytes_eq_append]
    simp only [List.append_assoc, List.cons_append, List.nil_append]; rfl

theorem seg3b_placed_runsTo [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_compress : H lsCompress256Sym = some (compress256Hook F))
    {key : List (BitVec 8)} {byte : BitVec 8} {s₀ s : State}
    (hpre : HmacPlacedPre F key [byte] s₀) (hs : StateH3cPlaced F key byte s₀ s) :
    RunsTo (lsProg_73 H) s (StateH4Placed F key byte s₀) := by
  generalize hPost : StateH4Placed F key byte s₀ = Post
  rcases hs with ⟨hpc, ⟨hstat, hsp_eq, hx29, hx27, hsaved, hframe⟩,
    hx0, hx1, hx2, hlr, hx19, hx20, host, hoblk⟩
  have hrw_hsp : s.mem.RW (hsp s₀) 480 :=
    ((hframe.rw_iff _ _).mpr hpre.rw_stack).sub (by unfold hsp; clear * -; bv_omega)
  refine RunsTo.placed_compress256_step h_compress
    (stPtr := hsp s₀ + 248#64) (blkPtr := hsp s₀ + 304#64) (lr := (blkPl_73).base + 620#64)
    (st := outerState F key) (blk := outerBlock (digestBytes (innerDigest F key byte)))
    (hrun := hstat) (hpc := hpc) (hx0 := hx0) (hx1 := hx1) (hx2 := hx2) (hlr := hlr)
    (hmem := rfl) (hst := host) (hblk := hoblk) (hrw := hrw_hsp.sub (by clear * -; bv_omega)) ?_
  subst hPost; refine RunsTo.refl ?_
  refine ⟨pc_setMem_setPC _ _ _, ⟨(status_setMem_setPC _ _ _).trans hstat,
    (sp_setMem_setPC _ _ _).trans hsp_eq, (readReg64_setMem_setPC _ _ _ _).trans hx29,
    (readReg64_setMem_setPC _ _ _ _).trans hx27, ?_, ?_⟩,
    (readReg64_setMem_setPC _ _ _ _).trans hx19, (readReg64_setMem_setPC _ _ _ _).trans hx20,
    read32_writeBytes_shaStateBytes s.mem (hsp s₀) 248#64 (outerDigest F key byte) 0,
    read32_writeBytes_shaStateBytes s.mem (hsp s₀) 248#64 (outerDigest F key byte) 1,
    read32_writeBytes_shaStateBytes s.mem (hsp s₀) 248#64 (outerDigest F key byte) 2,
    read32_writeBytes_shaStateBytes s.mem (hsp s₀) 248#64 (outerDigest F key byte) 3,
    read32_writeBytes_shaStateBytes s.mem (hsp s₀) 248#64 (outerDigest F key byte) 4,
    read32_writeBytes_shaStateBytes s.mem (hsp s₀) 248#64 (outerDigest F key byte) 5,
    read32_writeBytes_shaStateBytes s.mem (hsp s₀) 248#64 (outerDigest F key byte) 6,
    read32_writeBytes_shaStateBytes s.mem (hsp s₀) 248#64 (outerDigest F key byte) 7⟩
  · exact hsaved.of_agreesOutside (AgreesOutside.writeBytes_self _ _ _)
      (by simp only [shaStateBytes_length, DisjointRegions]; clear * -; bv_omega)
  · exact Frame.writeBytes_stack1024 hframe _ _ (by simp only [shaStateBytes_length]; unfold hsp; clear * -; bv_omega)

theorem seg3_placed_runsTo [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_compress : H lsCompress256Sym = some (compress256Hook F))
    {key : List (BitVec 8)} {byte : BitVec 8} {s₀ s : State}
    (hpre : HmacPlacedPre F key [byte] s₀) (hs : StateH3Placed F key byte s₀ s) :
    RunsTo (lsProg_73 H) s (StateH4Placed F key byte s₀) :=
  (seg3a_placed_runsTo hpre hs).trans (fun _ h3c => seg3b_placed_runsTo h_compress hpre h3c)

structure StateH4bPlaced [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (byte : BitVec 8) (s₀ s : State) : Prop where
  pc_eq  : s.pc = (blkPl_73).base + 744#64
  status : s.status = .Running
  sp_eq  : s.sp = hsp s₀
  x27_eq : s.readReg64 .x27 = s₀.readReg64 .x27
  saved  : HmacSaved s₀ (hsp s₀) s.mem
  out_eq : s.mem.readBytes (s₀.readReg64 .x0) 32 = hmacWith F key [byte]
  frame  : Frame s₀.mem s.mem [(s₀.readReg64 .x0, 32), (s₀.sp - 1024#64, 1024)]

theorem seg4a_placed_runsTo [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} {key : List (BitVec 8)} {byte : BitVec 8} {s₀ s : State}
    (hpre : HmacPlacedPre F key [byte] s₀) (hs : StateH4Placed F key byte s₀ s) :
    RunsTo (lsProg_73 H) s (StateH4bPlaced F key byte s₀) := by
  generalize hPost : StateH4bPlaced F key byte s₀ = Post
  rcases hs with ⟨hpc, ⟨hstat, hsp_eq, hx29, hx27, hsaved, hframe⟩, hx19, hx20, ho0, ho1, ho2, ho3, ho4, ho5, ho6, ho7⟩
  have hal_hsp : (hsp s₀ &&& 0b1111#64) = 0#64 := hsp_align hpre.sp_aligned
  have hrw_hsp : s.mem.RW (hsp s₀) 480 := ((hframe.rw_iff _ _).mpr hpre.rw_stack).sub (by unfold hsp; clear * -; bv_omega)
  have hrw_out : s.mem.RW (s₀.readReg64 .x0) 32 := (hframe.rw_iff _ _).mpr hpre.rw_out
  iterate 31 sess_step
  subst hPost; refine RunsTo.refl ?_
  have hframe1 : Frame s₀.mem
      (((((((((((((((((s.mem.write8 (hsp s₀ + 207#64) 0#8).write64 (hsp s₀ + 304#64) 0#64).write64
        (hsp s₀ + 312#64) 0#64).write64 (hsp s₀ + 320#64) 0#64).write64 (hsp s₀ + 328#64) 0#64).write64
        (hsp s₀ + 336#64) 0#64).write64 (hsp s₀ + 344#64) 0#64).write64 (hsp s₀ + 352#64) 0#64).write64
        (hsp s₀ + 360#64) 0#64).write64 (hsp s₀ + 192#64) 0#64).write64 (hsp s₀ + 200#64) 0#64).write64
        (hsp s₀ + 176#64) 0#64).write64 (hsp s₀ + 184#64) 0#64).write64 (hsp s₀ + 160#64) 0#64).write64
        (hsp s₀ + 168#64) 0#64).write64 (hsp s₀ + 144#64) 0#64).write64 (hsp s₀ + 152#64) 0#64)
      [(s₀.sp - 1024#64, 1024)] := by
    iterate 16 refine Frame.write64_stack1024 ?_ _ _
    exact Frame.write8_stack1024 hframe _ _
  refine ⟨by simp only [hpc, BitVec.add_assoc, BitVec.reduceAdd, arm64_norm],
    by simp only [arm64_norm, hstat], by simp only [arm64_norm, hsp_eq],
    by simp only [arm64_norm, hx27], ?_, ?_, ?_⟩
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    rw [write32_rev32_64_8_eq_writeBytes_digestBytes]
    have hsaved1 : HmacSaved s₀ (hsp s₀)
        (((((((((((((((((s.mem.write8 (hsp s₀ + 207#64) 0#8).write64 (hsp s₀ + 304#64) 0#64).write64
          (hsp s₀ + 312#64) 0#64).write64 (hsp s₀ + 320#64) 0#64).write64 (hsp s₀ + 328#64) 0#64).write64
          (hsp s₀ + 336#64) 0#64).write64 (hsp s₀ + 344#64) 0#64).write64 (hsp s₀ + 352#64) 0#64).write64
          (hsp s₀ + 360#64) 0#64).write64 (hsp s₀ + 192#64) 0#64).write64 (hsp s₀ + 200#64) 0#64).write64
          (hsp s₀ + 176#64) 0#64).write64 (hsp s₀ + 184#64) 0#64).write64 (hsp s₀ + 160#64) 0#64).write64
          (hsp s₀ + 168#64) 0#64).write64 (hsp s₀ + 144#64) 0#64).write64 (hsp s₀ + 152#64) 0#64) := by
      rcases hsaved with ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩
      dsimp only [HmacSaved]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11]
    exact hsaved1.of_agreesOutside (AgreesOutside.writeBytes_self _ _ _) (by
      have hd := hpre.disj_out_stack
      simp only [digestBytes_length, DisjointRegions, Reg.x0] at hd ⊢; unfold hsp; clear * - hd; bv_omega)
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    rw [write32_rev32_64_8_eq_writeBytes_digestBytes]
    have hread : ∀ m : Memory,
        (m.writeBytes (s₀.readReg64 .x0) (digestBytes (outerDigest F key byte))).readBytes
          (s₀.readReg64 .x0) 32 = digestBytes (outerDigest F key byte) :=
      fun m => Layout.readBytes_writeBytes_eq m _ _ 32 (digestBytes_length _) (by decide)
    rw [hread, hmacWith_short F key [byte] (by rw [hpre.key_len]; decide) (by simp)]
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    rw [write32_rev32_64_8_eq_writeBytes_digestBytes]
    exact Frame.writeBytes_out hframe1 _ (digestBytes_length _)

theorem seg4b_placed_runsTo [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} {key : List (BitVec 8)} {byte : BitVec 8} {s₀ s : State}
    (hpre : HmacPlacedPre F key [byte] s₀) (hs : StateH4bPlaced F key byte s₀ s) :
    RunsTo (lsProg_73 H) s (StateH5 F key byte s₀) := by
  generalize hPost : StateH5 F key byte s₀ = Post
  rcases hs with ⟨hpc, hstat, hsp_eq, hx27, hsaved, hout, hframe⟩
  rcases hsaved with ⟨s29, slr, s28, s26, s25, s24, s23, s22, s21, s20, s19⟩
  have hal_hsp : (hsp s₀ &&& 0b1111#64) = 0#64 := hsp_align hpre.sp_aligned
  have hrw_hsp : s.mem.RW (hsp s₀) 480 := ((hframe.rw_iff _ _).mpr hpre.rw_stack).sub (by unfold hsp; clear * -; bv_omega)
  iterate 8 sess_step
  subst hPost; refine RunsTo.refl ?_
  refine ⟨by simp only [arm64_norm, slr], by simp only [arm64_norm, hstat], ?_, hout, hframe⟩
  refine ⟨by simp only [arm64_norm, hsp_eq, ← hsp_eq_add], fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [arm64_norm, s19, s20, s21, s22, s23, s24, s25, s26, hx27, s28, s29, slr]

theorem seg4_placed_runsTo [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} {key : List (BitVec 8)} {byte : BitVec 8} {s₀ s : State}
    (hpre : HmacPlacedPre F key [byte] s₀) (hs : StateH4Placed F key byte s₀ s) :
    RunsTo (lsProg_73 H) s (StateH5 F key byte s₀) :=
  (seg4a_placed_runsTo hpre hs).trans (fun _ h4b => seg4b_placed_runsTo hpre h4b)

theorem hmac_placed_runsTo [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_memcpy : H lsMemcpySym = some memcpyHook)
    (h_memset : H lsMemsetSym = some memsetHook)
    (h_compress : H lsCompress256Sym = some (compress256Hook F))
    {key : List (BitVec 8)} {byte : BitVec 8} {s₀ : State}
    (hcl : LibsignalCodeLoaded lsmpl s₀.mem) (hpre : HmacPlacedPre F key [byte] s₀) :
    RunsTo (lsProg_73 H) s₀ (StateH5 F key byte s₀) :=
  (seg0_placed_runsTo h_memcpy h_compress hcl hpre).trans fun _ h1 =>
  (seg1a_placed_runsTo hpre h1).trans fun _ h1m =>
  (seg1b_placed_runsTo h_memcpy h_memset hpre h1m).trans fun _ h2 =>
  (seg2_placed_runsTo h_compress hpre h2).trans fun _ h3 =>
  (seg3_placed_runsTo h_compress hpre h3).trans fun _ h4 =>
  seg4_placed_runsTo hpre h4

end CryptoVerification.LibsignalSession.CryptoHmacSha256

