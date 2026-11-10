/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Hmac.Defs
public import LibsignalBinary.Specifications.LibsignalHmac
public import ProofLib.SepLogic.Frame
import LibsignalBinary.Proofs.AesCbc.Bytes

/-!
# SHA-256 chaining-state byte layout and endianness lemmas

Pure lemmas relating `shaStateBytes`, `readShaState`, `chunks64`, and 32-bit byte reversal (`rev`)
to big-endian SHA-256 digest words.
-/

@[expose] public section

namespace CryptoVerification
namespace LibsignalHmac
namespace OuterAux

open Arm64 ProofLib CryptoGames CryptoGames.HMAC
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister memcpyHook memsetHook toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run.Bytes

/-! ## `shaStateBytes`, `readShaState`, `chunks64`, and `compress256Hook` -/

theorem shaState_toList_eq (h : ShaState) :
    h.toList = [h.get 0, h.get 1, h.get 2, h.get 3, h.get 4, h.get 5, h.get 6, h.get 7] := by
  rcases h with ⟨l, hl⟩
  rcases l with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨w7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals (first | rfl | (simp at hl))

theorem shaStateBytes_eq_append (h : ShaState) :
    shaStateBytes h =
      toLEBytes 4 (h.get 0) ++ toLEBytes 4 (h.get 1) ++
      toLEBytes 4 (h.get 2) ++ toLEBytes 4 (h.get 3) ++
      toLEBytes 4 (h.get 4) ++ toLEBytes 4 (h.get 5) ++
      toLEBytes 4 (h.get 6) ++ toLEBytes 4 (h.get 7) := by
  unfold shaStateBytes
  rw [shaState_toList_eq]
  simp [List.flatMap_cons, List.flatMap_nil, List.append_assoc]

@[simp] theorem shaStateBytes_length (h : ShaState) :
    (shaStateBytes h).length = 32 := by
  rw [shaStateBytes_eq_append]
  simp [toLEBytes]

def bytesToU32LE (bs : List (BitVec 8)) : BitVec 32 :=
  bs.foldr (fun b acc => (acc <<< 8) ||| b.zeroExtend 32) 0

@[simp] theorem bytesToU32LE_toLEBytes_4 (w : BitVec 32) :
    bytesToU32LE (toLEBytes 4 w) = w := by
  dsimp only [bytesToU32LE, toLEBytes, List.ofFn, Fin.foldr, Fin.foldr.loop, List.foldr]
  bv_bits

theorem toLEBytes_4_read32 (m : Memory) (a : BitVec 64) :
    toLEBytes 4 (m.read32 a) = m.readBytes a 4 := by
  dsimp only [toLEBytes, List.ofFn, Fin.foldr, Fin.foldr.loop, List.foldr,
    Memory.read32, Memory.readBytes]
  simp only [BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd]
  refine List.cons_eq_cons.mpr ⟨by bv_bits, List.cons_eq_cons.mpr ⟨by bv_bits,
    List.cons_eq_cons.mpr ⟨by bv_bits, List.cons_eq_cons.mpr ⟨by bv_bits, rfl⟩⟩⟩⟩

theorem read32_eq_of_readBytes_eq_toLEBytes (m : Memory) (a : BitVec 64) (w : BitVec 32)
    (h : m.readBytes a 4 = toLEBytes 4 w) :
    m.read32 a = w := by
  rw [← bytesToU32LE_toLEBytes_4 w, ← h, ← toLEBytes_4_read32, bytesToU32LE_toLEBytes_4]

theorem shaStateBytes_slice_4 (h : ShaState) (i : Fin 8) :
    ((shaStateBytes h).drop (4 * i.val)).take 4 = toLEBytes 4 (h.get i) := by
  fin_cases i <;>
  · rw [shaStateBytes_eq_append]
    simp [toLEBytes_4_eq_list]

theorem read32_of_readBytes_shaStateBytes (m : Memory) (a : BitVec 64) (h : ShaState)
    (hm : m.readBytes a 32 = shaStateBytes h) (i : Fin 8) :
    m.read32 (a + BitVec.ofNat 64 (4 * i.val)) = h.get i := by
  apply read32_eq_of_readBytes_eq_toLEBytes
  have hlen : (shaStateBytes h).length = 32 := shaStateBytes_length h
  have hslice := readBytes_slice_of_readBytes_eq m a (shaStateBytes h)
    (by rw [hlen]; exact hm) (4 * i.val) 4 (by omega)
  rw [hslice, shaStateBytes_slice_4]

theorem readShaState_of_readBytes_shaStateBytes (m : Memory) (a : BitVec 64) (h : ShaState)
    (hm : m.readBytes a 32 = shaStateBytes h) :
    readShaState m a = h := by
  apply List.Vector.ext
  intro i
  simp only [readShaState, List.Vector.get_ofFn]
  exact read32_of_readBytes_shaStateBytes m a h hm i

theorem read32_writeBytes_shaStateBytes (m : Memory) (base off : BitVec 64) (h : ShaState)
    (i : Fin 8) :
    (m.writeBytes (base + off) (shaStateBytes h)).read32
      (base + (off + BitVec.ofNat 64 (4 * i.val))) = h.get i := by
  have hm : (m.writeBytes (base + off) (shaStateBytes h)).readBytes (base + off) 32 =
      shaStateBytes h := by
    simpa using ProofLib.readBytes_writeBytes_same m (base + off) (shaStateBytes h) (by simp)
  have hadd : base + (off + BitVec.ofNat 64 (4 * i.val)) =
      (base + off) + BitVec.ofNat 64 (4 * i.val) := by bv_omega
  rw [hadd]
  exact read32_of_readBytes_shaStateBytes _ (base + off) h hm i

private theorem list_ofFn_congr {α : Type} {m n : ℕ} (h : m = n) (f : Fin m → α) :
    List.ofFn f = List.ofFn (fun i : Fin n => f (i.cast h.symm)) := by
  subst h; rfl

theorem chunks64_of_length_64 {bs : List (BitVec 8)} (h : bs.length = 64) :
    chunks64 bs = [bs] := by
  unfold chunks64
  have hdiv : bs.length / 64 = 1 := by omega
  rw [list_ofFn_congr hdiv]
  simp [List.ofFn, Fin.foldr, Fin.foldr.loop, List.take_of_length_le (by omega : bs.length ≤ 64)]

theorem compress256Hook_eq_of_state_block (F : ShaState → List (BitVec 8) → ShaState)
    (s : State) (a b : BitVec 64) (st : ShaState) (blk : List (BitVec 8))
    (hx0 : s.readReg64 .x0 = a) (hx1 : s.readReg64 .x1 = b) (hx2 : s.readReg64 .x2 = 1#64)
    (hst : s.mem.readBytes a 32 = shaStateBytes st)
    (hblk : s.mem.readBytes b 64 = blk) :
    compress256Hook F s =
      returnToLinkRegister (s.setMem (s.mem.writeBytes a (shaStateBytes (F st blk)))) := by
  have hblk_len : blk.length = 64 := by
    rw [← hblk, Memory.readBytes_length]
  dsimp only [compress256Hook]
  rw [hx0, hx1, hx2, show 64 * (1#64 : BitVec 64).toNat = 64 from rfl,
    readShaState_of_readBytes_shaStateBytes s.mem a st hst, hblk,
    chunks64_of_length_64 hblk_len, List.foldl_cons, List.foldl_nil]

theorem agreesOutside_writeBytes_csp_sub (m : Memory) (e : MacEnv) (off : BitVec 64)
    (bs : List (BitVec 8)) (hle : off.toNat + bs.length ≤ 0x1d0) :
    AgreesOutside m (m.writeBytes (e.csp + off) bs) e.csp 0x1d0 := by
  refine AgreesOutside.writeBytes (AgreesOutside.rfl' m e.csp 0x1d0) ?_ (by decide)
  have hsub : (e.csp + off) - e.csp = off := by bv_omega
  rw [hsub]
  exact hle

/-! ## Endianness (`rev`) and digest byte lemmas -/

theorem toLEBytes_4_rev32_64_truncate (w : BitVec 32) :
    toLEBytes 4 ((rev32_64 (w.zeroExtend 64)).truncate 32) = toBEBytes 4 w := by
  have hr : (rev32_64 (w.zeroExtend 64)).truncate 32 =
      w.extractLsb' 0 8 ++ w.extractLsb' 8 8 ++ w.extractLsb' 16 8 ++ w.extractLsb' 24 8 := by
    simp only [rev32_64]; bv_bits
  rw [hr]
  dsimp only [toLEBytes, toBEBytes, List.ofFn, Fin.foldr, Fin.foldr.loop, List.foldr]
  generalize w.extractLsb' 0 8 = b0
  generalize w.extractLsb' 8 8 = b1
  generalize w.extractLsb' 16 8 = b2
  generalize w.extractLsb' 24 8 = b3
  refine List.cons_eq_cons.mpr ⟨by bv_bits, List.cons_eq_cons.mpr ⟨by bv_bits,
    List.cons_eq_cons.mpr ⟨by bv_bits, List.cons_eq_cons.mpr ⟨by bv_bits, rfl⟩⟩⟩⟩

theorem toLEBytes_8_rev64 (x : BitVec 64) :
    toLEBytes 8 (rev64 x) = toBEBytes 8 x := by
  dsimp only [toLEBytes, toBEBytes, rev64, List.ofFn, Fin.foldr, Fin.foldr.loop, List.foldr]
  generalize x.extractLsb' 0 8 = b0
  generalize x.extractLsb' 8 8 = b1
  generalize x.extractLsb' 16 8 = b2
  generalize x.extractLsb' 24 8 = b3
  generalize x.extractLsb' 32 8 = b4
  generalize x.extractLsb' 40 8 = b5
  generalize x.extractLsb' 48 8 = b6
  generalize x.extractLsb' 56 8 = b7
  refine List.cons_eq_cons.mpr ⟨by bv_bits, List.cons_eq_cons.mpr ⟨by bv_bits,
    List.cons_eq_cons.mpr ⟨by bv_bits, List.cons_eq_cons.mpr ⟨by bv_bits,
    List.cons_eq_cons.mpr ⟨by bv_bits, List.cons_eq_cons.mpr ⟨by bv_bits,
    List.cons_eq_cons.mpr ⟨by bv_bits, List.cons_eq_cons.mpr ⟨by bv_bits, rfl⟩⟩⟩⟩⟩⟩⟩⟩

theorem toLEBytes_8_rev64_pair (w0 w1 : BitVec 32) :
    toLEBytes 8 (rev64 (w1.zeroExtend 64 ||| (w0.zeroExtend 64 <<< 32))) =
      toBEBytes 4 w0 ++ toBEBytes 4 w1 := by
  have hp : w1.zeroExtend 64 ||| (w0.zeroExtend 64 <<< 32) = w0 ++ w1 := by bv_bits
  rw [hp, toLEBytes_8_rev64]
  dsimp only [toBEBytes, List.ofFn, Fin.foldr, Fin.foldr.loop, List.foldr,
    List.cons_append, List.nil_append]
  refine List.cons_eq_cons.mpr ⟨by bv_bits, List.cons_eq_cons.mpr ⟨by bv_bits,
    List.cons_eq_cons.mpr ⟨by bv_bits, List.cons_eq_cons.mpr ⟨by bv_bits,
    List.cons_eq_cons.mpr ⟨by bv_bits, List.cons_eq_cons.mpr ⟨by bv_bits,
    List.cons_eq_cons.mpr ⟨by bv_bits, List.cons_eq_cons.mpr ⟨by bv_bits, rfl⟩⟩⟩⟩⟩⟩⟩⟩

theorem shaState_be_eq_append (h : ShaState) :
    h.toList.flatMap (toBEBytes 4) =
      toBEBytes 4 (h.get 0) ++ toBEBytes 4 (h.get 1) ++
      toBEBytes 4 (h.get 2) ++ toBEBytes 4 (h.get 3) ++
      toBEBytes 4 (h.get 4) ++ toBEBytes 4 (h.get 5) ++
      toBEBytes 4 (h.get 6) ++ toBEBytes 4 (h.get 7) := by
  rw [shaState_toList_eq]
  simp [List.flatMap_cons, List.flatMap_nil, List.append_assoc]

theorem shaState_be_take_8 (h : ShaState) :
    (h.toList.flatMap (toBEBytes 4)).take 8 =
      toBEBytes 4 (h.get 0) ++ toBEBytes 4 (h.get 1) := by
  rw [shaState_be_eq_append]
  dsimp only [toBEBytes, List.ofFn, Fin.foldr, Fin.foldr.loop, List.foldr]
  rfl

end OuterAux
end LibsignalHmac
end CryptoVerification
