/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.GenDefs
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractCommon
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Kdf
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import ProofLib.SepLogic.WPp

/-!
# `spqr::kdf::hkdf_to_slice`: Extract Phase

Stack layout, frame invariants, and symbolic execution of the initial HKDF-Extract segments
(`0x63284 → 0x633cc`) of `spqr::kdf::hkdf_to_slice`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.SpqrV1.Kdf

open Arm64 ProofLib
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalAesCbc (memcpyHook memsetHook toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes)
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.CodeLayout

namespace HkdfToSliceProof

/-! ## Stack layout and frame helpers for `spqr::kdf::hkdf_to_slice` (`0x63284`) -/

attribute [scoped simp, arm64_norm]
  MemWidth.bytes SimdMemSize.bytes
  Memory.read8_write64_base_off_disjoint
  Memory.read64_write8_base_off_disjoint
  extractLsb'_56_8_read64

attribute [local simp, local arm64_norm] bv_sub_add_lit

@[scoped simp, arm64_norm] theorem read8_write64_264_271 (m : Memory) (base v : BitVec 64) :
    (m.write64 (base + 264#64) v).read8 (base + 271#64) = v.extractLsb' 56 8 := by
  dsimp only [Memory.write64]; simp [arm64_norm]

@[scoped simp, arm64_norm] theorem read8_write64_408_415 (m : Memory) (base v : BitVec 64) :
    (m.write64 (base + 408#64) v).read8 (base + 415#64) = v.extractLsb' 56 8 := by
  dsimp only [Memory.write64]; simp [arm64_norm]

@[simp, arm64_norm] private
gen_decodes libsignalSessionCode_tree libsignalSessionCode [0x5de8c → 0x5e108]

theorem hkdfExpand_32_eq (F : ShaState → List (BitVec 8) → ShaState) (prk info : List (BitVec 8)) :
    hkdfExpand F prk info 32 = Expand.t1 F prk info := by
  dsimp only [hkdfExpand]; have h1 : (32 + 31) / 32 = 1 := rfl
  have hblocks : (hkdfBlocks F prk info 1).flatten = Expand.t1 F prk info := by simp [hkdfBlocks, Expand.t1]
  rw [h1, hblocks, List.take_of_length_le]; simp [Expand.t1, length_hmacWith]

theorem hkdfExpand_96_eq (F : ShaState → List (BitVec 8) → ShaState) (prk info : List (BitVec 8)) :
    hkdfExpand F prk info 96 = Expand.t1 F prk info ++ Expand.t2 F prk info ++ Expand.t3 F prk info := by
  dsimp only [hkdfExpand]; have h3 : (96 + 31) / 32 = 3 := rfl
  have hblocks : (hkdfBlocks F prk info 3).flatten =
      Expand.t1 F prk info ++ Expand.t2 F prk info ++ Expand.t3 F prk info := by
    simp [hkdfBlocks, Expand.t1, Expand.t2, Expand.t3, List.append_assoc]
  rw [h3, hblocks, List.take_of_length_le]; simp [Expand.t1, Expand.t2, Expand.t3, length_hmacWith]

/-- Stack pointer of `spqr::kdf::hkdf_to_slice` after its 688-byte prologue (`96 + 592`). -/
def hsp (s₀ : State) : BitVec 64 := s₀.sp - 688#64

theorem hsp_eq_add (s₀ : State) : s₀.sp = hsp s₀ + 688#64 := by unfold hsp; bv_lin
@[scoped simp, arm64_norm] theorem sp_sub_688_eq_hsp (s₀ : State) : s₀.sp - 688#64 = hsp s₀ := rfl
@[scoped simp, arm64_norm] theorem sp_add_neg688_eq_hsp (s₀ : State) : s₀.sp + 18446744073709550928#64 = hsp s₀ := by unfold hsp; bv_lin
@[scoped simp, arm64_norm] theorem sp_sub_96_eq_hsp_592 (s₀ : State) : s₀.sp - 96#64 = hsp s₀ + 592#64 := by unfold hsp; bv_lin
@[scoped simp, arm64_norm] theorem sp_add_neg96_eq_hsp_592 (s₀ : State) : s₀.sp + 18446744073709551520#64 = hsp s₀ + 592#64 := by unfold hsp; bv_lin
@[scoped simp, arm64_norm] theorem hsp_592_sub_592_eq_hsp (s₀ : State) : (hsp s₀ + 592#64) - 592#64 = hsp s₀ := by bv_lin
@[scoped simp, arm64_norm] theorem hsp_592_add_neg592_eq_hsp (s₀ : State) : (hsp s₀ + 592#64) + 18446744073709551024#64 = hsp s₀ := by bv_lin
@[scoped simp, arm64_norm] theorem hsp_add_688_sub_688 (s₀ : State) : (hsp s₀ + 688#64) - 688#64 = hsp s₀ := by bv_lin

theorem hsp_aligned {s₀ : State} (hal : (s₀.sp &&& 15#64) = 0#64) :
    (hsp s₀ &&& 15#64) = 0#64 ∧ (hsp s₀ &&& 0b1111#64) = 0#64 ∧
    ((hsp s₀ + 592#64) &&& 15#64) = 0#64 ∧ ((hsp s₀ + 592#64) &&& 0b1111#64) = 0#64 := by
  have h1 : (hsp s₀ &&& 15#64) = 0#64 := by unfold hsp; bv_bits
  have h2 : ((hsp s₀ + 592#64) &&& 15#64) = 0#64 := by unfold hsp; bv_bits
  exact ⟨h1, h1, h2, h2⟩

/-- Saved callee-saved registers `x19..x30` at `hsp s₀ + 592 .. 688`. -/
structure HSaved (s₀ : State) (m : Memory) : Prop where
  m592 : m.read64 (hsp s₀ + 592#64) = s₀.readReg64 .x29
  m600 : m.read64 (hsp s₀ + 600#64) = s₀.readReg64 .lr
  m608 : m.read64 (hsp s₀ + 608#64) = s₀.readReg64 .x28
  m616 : m.read64 (hsp s₀ + 616#64) = s₀.readReg64 .x27
  m624 : m.read64 (hsp s₀ + 624#64) = s₀.readReg64 .x26
  m632 : m.read64 (hsp s₀ + 632#64) = s₀.readReg64 .x25
  m640 : m.read64 (hsp s₀ + 640#64) = s₀.readReg64 .x24
  m648 : m.read64 (hsp s₀ + 648#64) = s₀.readReg64 .x23
  m656 : m.read64 (hsp s₀ + 656#64) = s₀.readReg64 .x22
  m664 : m.read64 (hsp s₀ + 664#64) = s₀.readReg64 .x21
  m672 : m.read64 (hsp s₀ + 672#64) = s₀.readReg64 .x20
  m680 : m.read64 (hsp s₀ + 680#64) = s₀.readReg64 .x19

/-- Frame condition for `spqr::kdf::hkdf_to_slice`: only `[okmA .. okmA + okmLen)` and
`[hsp s₀ - 544#64 .. hsp s₀ + 688#64)` (`1232` bytes) are modified. -/
abbrev HFrame (okmLen : ℕ) (s₀ : State) (m : Memory) : Prop :=
  Frame s₀.mem m [(s₀.readReg64 .x6, okmLen), (hsp s₀ - 544#64, 1232)]

/-- Common state invariant across `spqr::kdf::hkdf_to_slice`. -/
structure HCommon (okmLen : ℕ) (s₀ s : State) : Prop where
  status : s.status = .Running
  sp_eq  : s.sp = hsp s₀
  x29_eq : s.readReg64 .x29 = hsp s₀ + 592#64
  saved  : HSaved s₀ s.mem
  frame  : HFrame okmLen s₀ s.mem

theorem HFrame.of_agreesOutside_hsp {okmLen : ℕ} {s₀ : State} {m m' : Memory}
    {off : BitVec 64} {sz : ℕ}
    (hf : HFrame okmLen s₀ m)
    (hA : AgreesOutside m m' (hsp s₀ + off) sz)
    (hoff : off.toNat + sz ≤ 688) :
    HFrame okmLen s₀ m' :=
  hf.trans_agreesOutside_sub (rbase := hsp s₀ - 544#64) (rlen := 1232) (by simp) (by clear * - hoff; bv_omega) hA

theorem HFrame.of_agreesOutside_okm {okmLen : ℕ} {s₀ : State} {m m' : Memory}
    {off : BitVec 64} {sz : ℕ}
    (hf : HFrame okmLen s₀ m)
    (hA : AgreesOutside m m' (s₀.readReg64 .x6 + off) sz)
    (hoff : off.toNat + sz ≤ okmLen) :
    HFrame okmLen s₀ m' :=
  hf.trans_agreesOutside_sub (rbase := s₀.readReg64 .x6) (rlen := okmLen) (by simp) (by clear * - hoff; bv_omega) hA

theorem HSaved.of_agreesOutside_low {s₀ : State} {m m' : Memory}
    {off : BitVec 64} {sz : ℕ}
    (hs : HSaved s₀ m)
    (hA : AgreesOutside m m' (hsp s₀ + off) sz)
    (hoff : 0 < sz ∧ off.toNat + sz ≤ 592) :
    HSaved s₀ m' := by
  have hread (k : BitVec 64) (hk : 592 ≤ k.toNat ∧ k.toNat + 8 ≤ 688) :
      m'.read64 (hsp s₀ + k) = m.read64 (hsp s₀ + k) := by
    refine hA.read64_eq ?_; rcases hoff with ⟨_, _⟩; rcases hk with ⟨_, _⟩; unfold DisjointRegions; bv_omega
  exact
    { m592 := (hread 592#64 (by decide)).trans hs.m592, m600 := (hread 600#64 (by decide)).trans hs.m600
      m608 := (hread 608#64 (by decide)).trans hs.m608, m616 := (hread 616#64 (by decide)).trans hs.m616
      m624 := (hread 624#64 (by decide)).trans hs.m624, m632 := (hread 632#64 (by decide)).trans hs.m632
      m640 := (hread 640#64 (by decide)).trans hs.m640, m648 := (hread 648#64 (by decide)).trans hs.m648
      m656 := (hread 656#64 (by decide)).trans hs.m656, m664 := (hread 664#64 (by decide)).trans hs.m664
      m672 := (hread 672#64 (by decide)).trans hs.m672, m680 := (hread 680#64 (by decide)).trans hs.m680 }

theorem agreesOutside_hsp_write64 {m₁ m₂ : Memory} {s₀ : State} {off w_off v : BitVec 64} {sz : ℕ}
    (h : AgreesOutside m₁ m₂ (hsp s₀ + off) sz)
    (hw : decide (off.toNat ≤ w_off.toNat ∧ w_off.toNat + 8 ≤ off.toNat + sz ∧ off.toNat + sz ≤ 688) = true) :
    AgreesOutside m₁ (m₂.write64 (hsp s₀ + w_off) v) (hsp s₀ + off) sz := by
  have ⟨h1, h2, h3⟩ := of_decide_eq_true hw
  exact h.write64 (by bv_omega) (by omega)

theorem agreesOutside_hsp_write8 {m₁ m₂ : Memory} {s₀ : State} {off w_off : BitVec 64}
    {v : BitVec 8} {sz : ℕ}
    (h : AgreesOutside m₁ m₂ (hsp s₀ + off) sz)
    (hw : decide (off.toNat ≤ w_off.toNat ∧ w_off.toNat + 1 ≤ off.toNat + sz ∧ off.toNat + sz ≤ 688) = true) :
    AgreesOutside m₁ (m₂.write8 (hsp s₀ + w_off) v) (hsp s₀ + off) sz := by
  have ⟨h1, h2, h3⟩ := of_decide_eq_true hw
  exact h.write8 (by simp only [InRegion]; bv_omega)

macro "prove_agrees_hsp" : tactic =>
  `(tactic| (
    repeat' rw [Expand.mem_setMem]
    repeat' (first
      | ((with_reducible refine agreesOutside_hsp_write64 ?_ ?hw); case hw => decide)
      | ((with_reducible refine AgreesOutside.write8 ?_ ?hw); case hw => (simp only [InRegion]; bv_omega)))
    exact AgreesOutside.rfl' _ _ _))

/-- `RunsTo` contract of `new_from_slice [local#3]` (`0x66fa0`) on `tripleRatchetProgAtExt b ext`
for a key slice at `s₀.x1` of length `(s₀.readReg64 .x2).toNat ≤ 64`. -/
def Nfs3RunsToExt (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (ext : String → Option (State → State)) : Prop :=
  ∀ {s₀ : State}, s₀.pc = b + 0x61ba8#64 → s₀.status = .Running → (s₀.readReg64 .x2).toNat ≤ 64 →
    s₀.mem.readBytes (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 = shaStateBytes sha256IV →
    (b &&& 0xfff#64) = 0#64 →
    s₀.mem.Readable (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 →
    DisjointRegions (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 (s₀.sp - 544#64) 544 →
    s₀.mem.RW (s₀.readReg64 .x0) 0x98 → s₀.mem.RW (s₀.sp - 544#64) 544 →
    DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544 →
    ((s₀.readReg64 .x2).toNat = 0 ∨ DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544) →
    (s₀.sp &&& 0b1111#64) = 0#64 →
    RunsTo (tripleRatchetProgAtExt b ext) s₀ (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧ s'.status = .Running ∧ CalleeSaved s₀ s' ∧
      s'.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧
      HmacSt s'.mem (s₀.readReg64 .x0 + 8#64) F (s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat) [] ∧
      Frame s₀.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 544#64, 544)])

/-- Bundled entry preconditions of `spqr::kdf::hkdf_to_slice` (`b + 0x63284`) across all SPQR V1
call sites (`salt.length < 2 ^ 63`, `ikm.length < 2 ^ 63`,
`32 ≤ info.length < 55`, `okmLen ∈ {32, 64, 96}`). -/
structure HPre (b : BitVec 64) (salt ikm info : List (BitVec 8))
    (saltA ikmA infoA okmA : BitVec 64) (okmLen : ℕ) (s₀ : State)
    (b_iv : BitVec 64 := b) (aligned : Prop := (b &&& 0xfff#64) = 0#64) : Prop where
  pc_eq         : s₀.pc = b + 0x5de8c#64
  status        : s₀.status = .Running
  x0_eq         : s₀.readReg64 .x0 = saltA
  x1_eq         : s₀.readReg64 .x1 = BitVec.ofNat 64 salt.length
  x2_eq         : s₀.readReg64 .x2 = ikmA
  x3_eq         : s₀.readReg64 .x3 = BitVec.ofNat 64 ikm.length
  x4_eq         : s₀.readReg64 .x4 = infoA
  x5_eq         : s₀.readReg64 .x5 = BitVec.ofNat 64 info.length
  x6_eq         : s₀.readReg64 .x6 = okmA
  x7_eq         : s₀.readReg64 .x7 = BitVec.ofNat 64 okmLen
  salt_lt       : salt.length < 2 ^ 63
  ikm_len       : ikm.length < 2 ^ 63
  info_ge       : 32 ≤ info.length
  info_lt       : info.length < 55
  okm_len       : okmLen = 32 ∨ okmLen = 64 ∨ okmLen = 96
  base_al       : aligned
  ro_iv_bytes   : s₀.mem.readBytes (b_iv + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 = shaStateBytes sha256IV
  ro_iv_read    : s₀.mem.Readable (b_iv + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32
  disj_iv_stk   : DisjointRegions (b_iv + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 (hsp s₀ - 544#64) 1232
  disj_iv_okm   : DisjointRegions (b_iv + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 okmA okmLen
  salt_bytes    : s₀.mem.readBytes saltA salt.length = salt
  ikm_bytes     : s₀.mem.readBytes ikmA ikm.length = ikm
  info_bytes    : s₀.mem.readBytes infoA info.length = info
  rw_okm        : RW s₀.mem okmA okmLen
  rw_stack      : RW s₀.mem (hsp s₀ - 544#64) 1232
  disj_okm_stk  : DisjointRegions okmA okmLen (hsp s₀ - 544#64) 1232
  disj_salt_stk : salt.length = 0 ∨ DisjointRegions saltA salt.length (hsp s₀ - 544#64) 1232
  out_salt_stk  : ∀ a, InRegion saltA salt.length a → OutsideRegion (hsp s₀ - 544#64) 1232 a
  out_salt_okm  : ∀ a, InRegion saltA salt.length a → OutsideRegion okmA okmLen a
  out_ikm_stk   : ∀ a, InRegion ikmA ikm.length a → OutsideRegion (hsp s₀ - 544#64) 1232 a
  out_ikm_okm   : ∀ a, InRegion ikmA ikm.length a → OutsideRegion okmA okmLen a
  out_info_stk  : ∀ a, InRegion infoA info.length a → OutsideRegion (hsp s₀ - 544#64) 1232 a
  out_info_okm  : ∀ a, InRegion infoA info.length a → OutsideRegion okmA okmLen a
  sp_aligned    : (s₀.sp &&& 15#64) = 0#64

theorem HFrame.keepsFrozen {b b_iv : BitVec 64} {aligned : Prop} {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ : State} {m : Memory}
    (hpre : HPre b salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (hf : HFrame okmLen s₀ m) :
    Expand.KeepsFrozenNoAnon s₀.mem m := by
  refine Expand.KeepsFrozenNoAnon.of_perm_eq hf.2.1 hf.2.2.2.1 fun a hperm => ?_
  refine hf.1 a (fun r hr => ?_)
  rw [outsideRegion_iff_not_inRegion]
  intro hin
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [hpre.x6_eq] at hin
    have hrw := (Memory.permNoLazy_eq_some_rw_iff.mp (hpre.rw_okm a hin)).1
    unfold Memory.Frozen at hperm; rw [hrw] at hperm; cases hperm
  · have hrw := (Memory.permNoLazy_eq_some_rw_iff.mp (hpre.rw_stack a hin)).1
    unfold Memory.Frozen at hperm; rw [hrw] at hperm; cases hperm

theorem HFrame.rw_hsp {b b_iv : BitVec 64} {aligned : Prop} {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ : State} {m : Memory}
    (hpre : HPre b salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (hf : HFrame okmLen s₀ m) :
    m.RW (hsp s₀) 688 := by
  have hrw : m.RW (hsp s₀ - 544#64) 1232 := (Expand.Frame.rw_iff hf _ _).mpr hpre.rw_stack
  exact hrw.sub (by bv_omega)

theorem HFrame.rw_sub_544 {b b_iv : BitVec 64} {aligned : Prop} {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ : State} {m : Memory}
    (hpre : HPre b salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (hf : HFrame okmLen s₀ m) :
    m.RW (hsp s₀ - 544#64) 544 := by
  have hrw : m.RW (hsp s₀ - 544#64) 1232 := (Expand.Frame.rw_iff hf _ _).mpr hpre.rw_stack
  exact hrw.sub (by bv_omega)

theorem HFrame.rw_okm {b b_iv : BitVec 64} {aligned : Prop} {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ : State} {m : Memory}
    (hpre : HPre b salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (hf : HFrame okmLen s₀ m) :
    m.RW okmA okmLen :=
  (Expand.Frame.rw_iff hf _ _).mpr hpre.rw_okm

theorem HFrame.ro_iv_read {b b_iv : BitVec 64} {aligned : Prop} {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ : State} {m : Memory}
    (hpre : HPre b salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (hf : HFrame okmLen s₀ m) :
    m.Readable (b_iv + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 :=
  (Expand.Frame.readable_iff hf _ _).mpr hpre.ro_iv_read

theorem HFrame.ro_iv_bytes {b b_iv : BitVec 64} {aligned : Prop} {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ : State} {m : Memory}
    (hpre : HPre b salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (hf : HFrame okmLen s₀ m) :
    m.readBytes (b_iv + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 = shaStateBytes sha256IV := by
  refine (Expand.Frame.readBytes_eq hf (fun r hr => ?_) (by decide)).trans hpre.ro_iv_bytes
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [hpre.x6_eq]; exact hpre.disj_iv_okm.symm
  · exact hpre.disj_iv_stk.symm

theorem HFrame.salt_bytes {b b_iv : BitVec 64} {aligned : Prop} {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ : State} {m : Memory}
    (hpre : HPre b salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (hf : HFrame okmLen s₀ m) :
    m.readBytes saltA salt.length = salt := by
  refine (List.ext_getElem (by simp) fun i h1 h2 => ?_).trans hpre.salt_bytes
  rw [Bytes.readBytes_getElem _ _ _ i h1, Bytes.readBytes_getElem _ _ _ i h2]
  have hi : i < salt.length := by simpa using h1
  have hin : InRegion saltA salt.length (saltA + BitVec.ofNat 64 i) :=
    inRegion_base_add saltA salt.length i hi (by have := hpre.salt_lt; omega)
  refine hf.1 _ (fun r hr => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [hpre.x6_eq]; exact hpre.out_salt_okm _ hin
  · exact hpre.out_salt_stk _ hin

theorem HFrame.ikm_bytes {b b_iv : BitVec 64} {aligned : Prop} {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ : State} {m : Memory}
    (hpre : HPre b salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (hf : HFrame okmLen s₀ m) :
    m.readBytes ikmA ikm.length = ikm := by
  refine (List.ext_getElem (by simp) fun i h1 h2 => ?_).trans hpre.ikm_bytes
  rw [Bytes.readBytes_getElem _ _ _ i h1, Bytes.readBytes_getElem _ _ _ i h2]
  have hi : i < ikm.length := by simpa using h1
  have hin : InRegion ikmA ikm.length (ikmA + BitVec.ofNat 64 i) :=
    inRegion_base_add ikmA ikm.length i hi (by have := hpre.ikm_len; omega)
  refine hf.1 _ (fun r hr => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [hpre.x6_eq]; exact hpre.out_ikm_okm _ hin
  · exact hpre.out_ikm_stk _ hin

theorem HFrame.info_bytes {b b_iv : BitVec 64} {aligned : Prop} {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ : State} {m : Memory}
    (hpre : HPre b salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (hf : HFrame okmLen s₀ m) :
    m.readBytes infoA info.length = info := by
  refine (List.ext_getElem (by simp) fun i h1 h2 => ?_).trans hpre.info_bytes
  rw [Bytes.readBytes_getElem _ _ _ i h1, Bytes.readBytes_getElem _ _ _ i h2]
  have hi : i < info.length := by simpa using h1
  have hin : InRegion infoA info.length (infoA + BitVec.ofNat 64 i) :=
    inRegion_base_add infoA info.length i hi (by have := hpre.info_lt; omega)
  refine hf.1 _ (fun r hr => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [hpre.x6_eq]; exact hpre.out_info_okm _ hin
  · exact hpre.out_info_stk _ hin

theorem HSaved.of_agreesOutside_okm {b b_iv : BitVec 64} {aligned : Prop} {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ : State} {m m' : Memory}
    {off : BitVec 64} {sz : ℕ}
    (hpre : HPre b salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (hs : HSaved s₀ m)
    (hA : AgreesOutside m m' (okmA + off) sz)
    (hoff : 0 < sz ∧ off.toNat + sz ≤ okmLen) :
    HSaved s₀ m' := by
  have hd_okm_saved : DisjointRegions (okmA + off) sz (hsp s₀ + 592#64) 96 := by
    have hd1 := hpre.disj_okm_stk.sub_left (okmA + off)
      ⟨hoff.1, by have := hoff.2; have := hpre.okm_len; bv_omega⟩
    exact hd1.sub_right (hsp s₀ + 592#64) ⟨by decide, by bv_omega⟩
  have hread (k : BitVec 64) (hk : 592 ≤ k.toNat ∧ k.toNat + 8 ≤ 688) :
      m'.read64 (hsp s₀ + k) = m.read64 (hsp s₀ + k) := by
    refine hA.read64_eq (hd_okm_saved.sub_right (hsp s₀ + k) ⟨by decide, ?_⟩)
    rcases hk with ⟨_, _⟩; bv_omega
  exact
    { m592 := (hread 592#64 (by decide)).trans hs.m592, m600 := (hread 600#64 (by decide)).trans hs.m600
      m608 := (hread 608#64 (by decide)).trans hs.m608, m616 := (hread 616#64 (by decide)).trans hs.m616
      m624 := (hread 624#64 (by decide)).trans hs.m624, m632 := (hread 632#64 (by decide)).trans hs.m632
      m640 := (hread 640#64 (by decide)).trans hs.m640, m648 := (hread 648#64 (by decide)).trans hs.m648
      m656 := (hread 656#64 (by decide)).trans hs.m656, m664 := (hread 664#64 (by decide)).trans hs.m664
      m672 := (hread 672#64 (by decide)).trans hs.m672, m680 := (hread 680#64 (by decide)).trans hs.m680 }

theorem HCommon.of_agreesOutside_hsp {okmLen : ℕ} {s₀ s s' : State}
    {off : BitVec 64} {sz : ℕ}
    (hc : HCommon okmLen s₀ s)
    (hstat : s'.status = .Running)
    (hsp_eq : s'.sp = hsp s₀)
    (hx29 : s'.readReg64 .x29 = hsp s₀ + 592#64)
    (hA : AgreesOutside s.mem s'.mem (hsp s₀ + off) sz)
    (hoff : decide (0 < sz ∧ off.toNat + sz ≤ 592) = true) :
    HCommon okmLen s₀ s' := by
  have ⟨h1, h2⟩ : 0 < sz ∧ off.toNat + sz ≤ 592 := of_decide_eq_true hoff
  exact ⟨hstat, hsp_eq, hx29,
    HSaved.of_agreesOutside_low hc.saved hA ⟨h1, h2⟩,
    HFrame.of_agreesOutside_hsp hc.frame hA (by omega)⟩

theorem HCommon.of_agreesOutside_okm {b b_iv : BitVec 64} {aligned : Prop} {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s s' : State}
    {off : BitVec 64} {sz : ℕ}
    (hpre : HPre b salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (hc : HCommon okmLen s₀ s)
    (hstat : s'.status = .Running)
    (hsp_eq : s'.sp = hsp s₀)
    (hx29 : s'.readReg64 .x29 = hsp s₀ + 592#64)
    (hA : AgreesOutside s.mem s'.mem (okmA + off) sz)
    (hoff : 0 < sz ∧ off.toNat + sz ≤ okmLen) :
    HCommon okmLen s₀ s' := by
  have hA' : AgreesOutside s.mem s'.mem (s₀.readReg64 .x6 + off) sz := by
    rw [hpre.x6_eq]; exact hA
  exact ⟨hstat, hsp_eq, hx29,
    HSaved.of_agreesOutside_okm hpre hc.saved hA hoff,
    HFrame.of_agreesOutside_okm hc.frame hA' hoff.2⟩

theorem HCommon.of_nfs_frame {okmLen : ℕ} {s₀ s s' : State} {retOff : BitVec 64}
    (hc : HCommon okmLen s₀ s)
    (hstat : s'.status = .Running)
    (hcs : CalleeSaved s s')
    (hfr : Frame s.mem s'.mem [(hsp s₀ + retOff, 0x98), (hsp s₀ - 544#64, 544)])
    (hret : decide (retOff.toNat + 0x98 ≤ 592) = true) :
    HCommon okmLen s₀ s' := by
  have hret' : retOff.toNat + 0x98 ≤ 592 := of_decide_eq_true hret
  have hd_saved : ∀ r ∈ [(hsp s₀ + retOff, (0x98 : ℕ)), (hsp s₀ - 544#64, 544)],
      DisjointRegions r.1 r.2 (hsp s₀ + 592#64) 96 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (unfold DisjointRegions; bv_omega)
  have h_saved_eq : ∀ (off : BitVec 64),
      decide (592 ≤ off.toNat ∧ off.toNat + 8 ≤ 688) = true →
      s'.mem.read64 (hsp s₀ + off) = s.mem.read64 (hsp s₀ + off) := by
    intro off hoff
    have ⟨h1, h2⟩ := of_decide_eq_true hoff
    refine Expand.Frame.read64_eq hfr fun r hr => ?_
    exact (hd_saved r hr).sub_right (hsp s₀ + off) ⟨by decide, by bv_omega⟩
  rcases hc.saved with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  have hsaved' : HSaved s₀ s'.mem :=
    { m592 := (h_saved_eq 592#64 (by decide)).trans h0, m600 := (h_saved_eq 600#64 (by decide)).trans h1
      m608 := (h_saved_eq 608#64 (by decide)).trans h2, m616 := (h_saved_eq 616#64 (by decide)).trans h3
      m624 := (h_saved_eq 624#64 (by decide)).trans h4, m632 := (h_saved_eq 632#64 (by decide)).trans h5
      m640 := (h_saved_eq 640#64 (by decide)).trans h6, m648 := (h_saved_eq 648#64 (by decide)).trans h7
      m656 := (h_saved_eq 656#64 (by decide)).trans h8, m664 := (h_saved_eq 664#64 (by decide)).trans h9
      m672 := (h_saved_eq 672#64 (by decide)).trans h10, m680 := (h_saved_eq 680#64 (by decide)).trans h11 }
  have hframe' : HFrame okmLen s₀ s'.mem := by
    refine Frame.trans hc.frame (Frame.mono hfr ?_)
    intro a ha r hr
    have hstack := ha (hsp s₀ - 544#64, 1232) (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (unfold OutsideRegion at *; bv_omega)
  exact ⟨hstat, hcs.sp_eq.trans hc.sp_eq, (CalleeSaved.x29 hcs).trans hc.x29_eq, hsaved', hframe'⟩

theorem HCommon.of_fin_frame {okmLen : ℕ} {s₀ s s' : State} {outOff : BitVec 64}
    (hc : HCommon okmLen s₀ s)
    (hstat : s'.status = .Running)
    (hcs : CalleeSaved s s')
    (hfr : Frame s.mem s'.mem [(hsp s₀ + outOff, 32), (hsp s₀ + 32#64, 0x90), (hsp s₀ - 144#64, 144)])
    (hout : decide (outOff.toNat + 32 ≤ 592) = true) :
    HCommon okmLen s₀ s' := by
  have hout' : outOff.toNat + 32 ≤ 592 := of_decide_eq_true hout
  have hd_saved : ∀ r ∈ [(hsp s₀ + outOff, (32 : ℕ)), (hsp s₀ + 32#64, 0x90), (hsp s₀ - 144#64, 144)],
      DisjointRegions r.1 r.2 (hsp s₀ + 592#64) 96 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (unfold DisjointRegions; bv_omega)
  have h_saved_eq : ∀ (off : BitVec 64),
      decide (592 ≤ off.toNat ∧ off.toNat + 8 ≤ 688) = true →
      s'.mem.read64 (hsp s₀ + off) = s.mem.read64 (hsp s₀ + off) := by
    intro off hoff
    have ⟨h1, h2⟩ := of_decide_eq_true hoff
    refine Expand.Frame.read64_eq hfr fun r hr => ?_
    exact (hd_saved r hr).sub_right (hsp s₀ + off) ⟨by decide, by bv_omega⟩
  rcases hc.saved with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  have hsaved' : HSaved s₀ s'.mem :=
    { m592 := (h_saved_eq 592#64 (by decide)).trans h0, m600 := (h_saved_eq 600#64 (by decide)).trans h1
      m608 := (h_saved_eq 608#64 (by decide)).trans h2, m616 := (h_saved_eq 616#64 (by decide)).trans h3
      m624 := (h_saved_eq 624#64 (by decide)).trans h4, m632 := (h_saved_eq 632#64 (by decide)).trans h5
      m640 := (h_saved_eq 640#64 (by decide)).trans h6, m648 := (h_saved_eq 648#64 (by decide)).trans h7
      m656 := (h_saved_eq 656#64 (by decide)).trans h8, m664 := (h_saved_eq 664#64 (by decide)).trans h9
      m672 := (h_saved_eq 672#64 (by decide)).trans h10, m680 := (h_saved_eq 680#64 (by decide)).trans h11 }
  have hframe' : HFrame okmLen s₀ s'.mem := by
    refine Frame.trans hc.frame (Frame.mono hfr ?_)
    intro a ha r hr
    have hstack := ha (hsp s₀ - 544#64, 1232) (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (unfold OutsideRegion at *; bv_omega)
  exact ⟨hstat, hcs.sp_eq.trans hc.sp_eq, (CalleeSaved.x29 hcs).trans hc.x29_eq, hsaved', hframe'⟩

/-! ## Extract-Phase Cut Predicates (`0x63284 → 0x634fc`) -/

structure StateENfs1 (b : BitVec 64) (salt ikm info : List (BitVec 8))
    (saltA ikmA infoA okmA : BitVec 64) (okmLen : ℕ) (s₀ s : State)
    (pc_target : BitVec 64 := b + 0x61ba8#64) : Prop where
  pc_eq  : s.pc = pc_target
  common : HCommon okmLen s₀ s
  lr_eq  : s.readReg64 .lr = b + 0x5ded4#64
  x0_eq  : s.readReg64 .x0 = hsp s₀ + 32#64
  x1_eq  : s.readReg64 .x1 = saltA
  x2_eq  : s.readReg64 .x2 = BitVec.ofNat 64 salt.length
  x22_eq : s.readReg64 .x22 = okmA
  x23_eq : s.readReg64 .x23 = ikmA
  x24_eq : s.readReg64 .x24 = BitVec.ofNat 64 ikm.length
  x25_eq : s.readReg64 .x25 = BitVec.ofNat 64 info.length
  x26_eq : s.readReg64 .x26 = BitVec.ofNat 64 okmLen
  x27_eq : s.readReg64 .x27 = infoA

structure StateERet1 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (ikmA infoA okmA : BitVec 64) (okmLen : ℕ)
    (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + 0x5ded4#64
  common  : HCommon okmLen s₀ s
  x22_eq  : s.readReg64 .x22 = okmA
  x23_eq  : s.readReg64 .x23 = ikmA
  x24_eq  : s.readReg64 .x24 = BitVec.ofNat 64 ikm.length
  x25_eq  : s.readReg64 .x25 = BitVec.ofNat 64 info.length
  x26_eq  : s.readReg64 .x26 = BitVec.ofNat 64 okmLen
  x27_eq  : s.readReg64 .x27 = infoA
  tag_32  : s.mem.read64 (hsp s₀ + 32#64) = 0#64
  hmac_40 : HmacSt s.mem (hsp s₀ + 40#64) F (effectiveHmacKey F salt) []

structure StateE3cc (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (infoA okmA : BitVec 64) (okmLen : ℕ)
    (s₀ s : State) : Prop where
  pc_eq    : s.pc = b + 0x5dfd4#64
  common   : HCommon okmLen s₀ s
  x19_eq   : s.readReg64 .x19 = hsp s₀ + 208#64
  x22_eq   : s.readReg64 .x22 = okmA
  x25_eq   : s.readReg64 .x25 = BitVec.ofNat 64 info.length
  x26_eq   : s.readReg64 .x26 = BitVec.ofNat 64 okmLen
  x27_eq   : s.readReg64 .x27 = infoA
  m16_eq   : s.mem.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length
  hmac_208 : ∃ pfx tail, pfx ++ tail = ikm ∧ pfx.length % 64 = 0 ∧ tail.length < 64 ∧
               HmacStN s.mem (hsp s₀ + 208#64) F (effectiveHmacKey F salt) pfx tail

structure StateEFin (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (infoA okmA : BitVec 64) (okmLen : ℕ)
    (s₀ s : State) (pc_target : BitVec 64 := b + 0x67a58#64) : Prop where
  pc_eq   : s.pc = pc_target
  common  : HCommon okmLen s₀ s
  lr_eq   : s.readReg64 .lr = b + 0x5e008#64
  x0_eq   : s.readReg64 .x0 = hsp s₀ + 507#64
  x1_eq   : s.readReg64 .x1 = hsp s₀ + 32#64
  x19_eq  : s.readReg64 .x19 = hsp s₀ + 208#64
  x22_eq  : s.readReg64 .x22 = okmA
  x25_eq  : s.readReg64 .x25 = BitVec.ofNat 64 info.length
  x26_eq  : s.readReg64 .x26 = BitVec.ofNat 64 okmLen
  x27_eq  : s.readReg64 .x27 = infoA
  m16_eq  : s.mem.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length
  hmac_32 : ∃ pfx tail, pfx ++ tail = ikm ∧ pfx.length % 64 = 0 ∧ tail.length < 64 ∧
              HmacStN s.mem (hsp s₀ + 32#64) F (effectiveHmacKey F salt) pfx tail

structure StateERetFin (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (infoA okmA : BitVec 64) (okmLen : ℕ)
    (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + 0x5e008#64
  common  : HCommon okmLen s₀ s
  x19_eq  : s.readReg64 .x19 = hsp s₀ + 208#64
  x22_eq  : s.readReg64 .x22 = okmA
  x25_eq  : s.readReg64 .x25 = BitVec.ofNat 64 info.length
  x26_eq  : s.readReg64 .x26 = BitVec.ofNat 64 okmLen
  x27_eq  : s.readReg64 .x27 = infoA
  m16_eq  : s.mem.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length
  prk_507 : s.mem.readBytes (hsp s₀ + 507#64) 32 = hkdfExtractBytes F salt ikm

structure StateENfs2 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (infoA okmA : BitVec 64) (okmLen : ℕ)
    (s₀ s : State) (pc_target : BitVec 64 := b + 0x61ba8#64) : Prop where
  pc_eq   : s.pc = pc_target
  common  : HCommon okmLen s₀ s
  lr_eq   : s.readReg64 .lr = b + 0x5e018#64
  x0_eq   : s.readReg64 .x0 = hsp s₀ + 352#64
  x1_eq   : s.readReg64 .x1 = hsp s₀ + 507#64
  x2_eq   : s.readReg64 .x2 = 32#64
  x19_eq  : s.readReg64 .x19 = hsp s₀ + 208#64
  x22_eq  : s.readReg64 .x22 = okmA
  x25_eq  : s.readReg64 .x25 = BitVec.ofNat 64 info.length
  x26_eq  : s.readReg64 .x26 = BitVec.ofNat 64 okmLen
  x27_eq  : s.readReg64 .x27 = infoA
  m16_eq  : s.mem.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length
  prk_507 : s.mem.readBytes (hsp s₀ + 507#64) 32 = hkdfExtractBytes F salt ikm

structure StateERet2 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (infoA okmA : BitVec 64) (okmLen : ℕ)
    (s₀ s : State) : Prop where
  pc_eq    : s.pc = b + 0x5e018#64
  common   : HCommon okmLen s₀ s
  x19_eq   : s.readReg64 .x19 = hsp s₀ + 208#64
  x22_eq   : s.readReg64 .x22 = okmA
  x25_eq   : s.readReg64 .x25 = BitVec.ofNat 64 info.length
  x26_eq   : s.readReg64 .x26 = BitVec.ofNat 64 okmLen
  x27_eq   : s.readReg64 .x27 = infoA
  m16_eq   : s.mem.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length
  tag_352  : s.mem.read64 (hsp s₀ + 352#64) = 0#64
  hmac_360 : HmacSt s.mem (hsp s₀ + 360#64) F (hkdfExtractBytes F salt ikm) []

/-- Cut `StateExtractDone` at `b + 0x634fc` (entry to the Expand phase, reached in 34 steps from `0x63410`):
- `Hmac(PRK, [])` template is stored at `hsp s₀ + 208#64` (`x19`)
- `[sp + 0] = okmLen`, `[sp + 8] = infoA`, `[sp + 16] = info.length`
- `x22 = okmA`, `x25 = info.length`, `x26 = okmLen`, `x27 = infoA`. -/
structure StateExtractDone (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (infoA okmA : BitVec 64) (okmLen : ℕ)
    (s₀ s : State) : Prop where
  pc_eq    : s.pc = b + 0x5e104#64
  common   : HCommon okmLen s₀ s
  x19_eq   : s.readReg64 .x19 = hsp s₀ + 208#64
  x22_eq   : s.readReg64 .x22 = okmA
  x25_eq   : s.readReg64 .x25 = BitVec.ofNat 64 info.length
  x26_eq   : s.readReg64 .x26 = BitVec.ofNat 64 okmLen
  x27_eq   : s.readReg64 .x27 = infoA
  m0_eq    : s.mem.read64 (hsp s₀ + 0#64) = BitVec.ofNat 64 okmLen
  m8_eq    : s.mem.read64 (hsp s₀ + 8#64) = infoA
  m16_eq   : s.mem.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length
  hmac_208 : HmacSt s.mem (hsp s₀ + 208#64) F (hkdfExtractBytes F salt ikm) []

/-! ## Placed Code Fake Base (`hkdfCodeFakeB`) & Hook Step Helpers (Block `379`) -/

@[local simp, local arm64_norm]
abbrev hkdfCodeFakeB [LibsignalPlacement] : BitVec 64 := (blkPl_379).base - 0x5de8c#64

@[local simp, local arm64_norm]
theorem bv_sub_add_lit_ge (x : BitVec 64) (a b : Nat) (h : a ≤ b := by decide)
    (hb : b < 2 ^ 64 := by decide) :
    x - BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (b - a) := by
  have heq : BitVec.ofNat 64 b = BitVec.ofNat 64 a + BitVec.ofNat 64 (b - a) := by
    rw [← BitVec.ofNat_add, Nat.add_sub_of_le h]
  rw [heq, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem s2_memcpy_step_placed_429 [LibsignalPlacement] {H_arg : LibsignalHooks}
    (h_memcpy : H_arg lsMemcpySym = some memcpyHook)
    {s₀ s : State} {Q : State → Prop}
    {dst src lr : BitVec 64} {len : ℕ} {bs : List (BitVec 8)}
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsMemcpySym)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hbs : s.mem.readBytes src len = bs)
    (hrw : s.mem.RW dst len)
    (h : RunsToFrom ((blkPC_379).rebase (blkPl_379).base H_arg) s₀
      ((s.setMem (s.mem.writeBytes dst bs)).setPC lr) Q) :
    RunsToFrom ((blkPC_379).rebase (blkPl_379).base H_arg) s₀ s Q := by
  have hcan : s.mem.canWrite dst bs.length = true := by
    rw [← hbs, Memory.readBytes_length]
    exact hrw.canWrite_sub (by simp) (by omega)
  have hhook : ((blkPC_379).rebase (blkPl_379).base H_arg).externAt? s.pc = some memcpyHook := by
    rw [hpc]
    exact (Alloc.spqr_externAt?_of_mem (sym := lsMemcpySym)).trans h_memcpy
  have hstate : memcpyHook s = (s.setMem (s.mem.writeBytes dst bs)).setPC lr :=
    memcpyHook_eq hx0 hx1 hx2 hlr hbs
  have hkeep : s.mem.KeepsFrozen (memcpyHook s).mem := by
    rw [hstate]; exact Memory.keepsFrozen_writeBytes _ hcan
  have hsym : (memcpyHook s).symtab = s.symtab := by rw [hstate]; rfl
  refine RunsTo.hook hrun hhook hkeep hsym ?_
  rwa [hstate]

theorem s2_compress256_multi_step_placed_429 [LibsignalPlacement] {C_arg : Crypto} {H_arg : LibsignalHooks}
    (h_compress : H_arg lsCompress256Sym = some (compress256Hook C_arg.F))
    {s₀ s : State} {Q : State → Prop}
    {stPtr blkPtr lr : BitVec 64} {st st' : ShaState} {nBlocks : ℕ} {pfx : List (BitVec 8)}
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsCompress256Sym)
    (hx0 : s.readReg64 .x0 = stPtr)
    (hx1 : s.readReg64 .x1 = blkPtr)
    (hx2 : (s.readReg64 .x2).toNat = nBlocks)
    (hlr : s.readReg64 .lr = lr)
    (hst : s.mem.readBytes stPtr 32 = shaStateBytes st)
    (hblk : s.mem.readBytes blkPtr (64 * nBlocks) = pfx)
    (hst' : (chunks64 pfx).foldl C_arg.F st = st')
    (hrw : s.mem.RW stPtr 32)
    (h : RunsToFrom ((blkPC_379).rebase (blkPl_379).base H_arg) s₀
      ((s.setMem (s.mem.writeBytes stPtr (shaStateBytes st'))).setPC lr) Q) :
    RunsToFrom ((blkPC_379).rebase (blkPl_379).base H_arg) s₀ s Q := by
  have hcan : s.mem.canWrite stPtr (shaStateBytes st').length = true := by
    rw [shaStateBytes_length]
    exact hrw.canWrite_sub (by simp) (by decide)
  have hhook : ((blkPC_379).rebase (blkPl_379).base H_arg).externAt? s.pc = some (compress256Hook C_arg.F) := by
    rw [hpc]
    exact (Alloc.spqr_externAt?_of_mem (sym := lsCompress256Sym)).trans h_compress
  have hstate : compress256Hook C_arg.F s =
      (s.setMem (s.mem.writeBytes stPtr (shaStateBytes st'))).setPC lr := by
    rw [compress256Hook_multi_eq C_arg.F hx0 hx1 hx2 hlr hst hblk, hst']
  have hkeep : s.mem.KeepsFrozen (compress256Hook C_arg.F s).mem := by
    rw [hstate]; exact Memory.keepsFrozen_writeBytes _ hcan
  have hsym : (compress256Hook C_arg.F s).symtab = s.symtab := by rw [hstate]; rfl
  refine RunsTo.hook hrun hhook hkeep hsym ?_
  rwa [hstate]

theorem s2_compress256_step_placed_429 [LibsignalPlacement] {C_arg : Crypto} {H_arg : LibsignalHooks}
    (h_compress : H_arg lsCompress256Sym = some (compress256Hook C_arg.F))
    {s₀ s : State} {Q : State → Prop}
    {stPtr blkPtr lr : BitVec 64} {st : ShaState} {blk : List (BitVec 8)}
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsCompress256Sym)
    (hx0 : s.readReg64 .x0 = stPtr)
    (hx1 : s.readReg64 .x1 = blkPtr)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hlr : s.readReg64 .lr = lr)
    (hst : s.mem.readBytes stPtr 32 = shaStateBytes st)
    (hblk : s.mem.readBytes blkPtr 64 = blk)
    (hlen : blk.length = 64)
    (hrw : s.mem.RW stPtr 32)
    (h : RunsToFrom ((blkPC_379).rebase (blkPl_379).base H_arg) s₀
      ((s.setMem (s.mem.writeBytes stPtr (shaStateBytes (C_arg.F st blk)))).setPC lr) Q) :
    RunsToFrom ((blkPC_379).rebase (blkPl_379).base H_arg) s₀ s Q :=
  s2_compress256_multi_step_placed_429 h_compress (nBlocks := 1)
    hrun hpc hx0 hx1 (by rw [hx2]; rfl) hlr hst hblk
    (by rw [chunks64_single_64 hlen]; rfl) hrw h

/-- Generalized `RunsTo` contract of `new_from_slice [local#3]` parameterized over `P`, `b_iv`, `pc_nfs`, `aligned`. -/
def Nfs3GenRunsToProg (P : Program) (b_iv pc_nfs : BitVec 64) (aligned : Memory → Prop)
    (F : ShaState → List (BitVec 8) → ShaState) : Prop :=
  ∀ {s₀ : State},
    s₀.pc = pc_nfs →
    s₀.status = .Running →
    (s₀.readReg64 .x2).toNat < 2 ^ 63 →
    s₀.mem.readBytes (b_iv + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 = shaStateBytes sha256IV →
    aligned s₀.mem →
    s₀.mem.Readable (b_iv + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 →
    DisjointRegions (b_iv + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 (s₀.sp - 544#64) 544 →
    s₀.mem.RW (s₀.readReg64 .x0) 0x98 →
    s₀.mem.RW (s₀.sp - 544#64) 544 →
    DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544 →
    ((s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544) →
    ((s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.readReg64 .x0) 0x98) →
    (s₀.sp &&& 0b1111#64) = 0#64 →
    RunsTo P s₀ (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧
      s'.status = .Running ∧
      CalleeSaved s₀ s' ∧
      s'.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧
      HmacSt s'.mem (s₀.readReg64 .x0 + 8#64) F
        (effectiveHmacKey F (s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat)) [] ∧
      Frame s₀.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 544#64, 544)])

/-! ## Extract-Phase Segment Proofs (`0x63284 → 0x634fc`) -/

macro "kdf_step" : tactic =>
  `(tactic| (
    refine RunsTo.step (inst := ?inst) ?hrun ?hfetch ?_
    case hfetch => (
      (try simp (config := { decide := true }) only [arm64_norm, *])
      first
      | (refine libsignalSessionCode_fetch_rebase_text ?_ (by decide) (by decide)
         (try simp only [arm64_norm]) <;> rfl)
      | rfl)
    case hrun => (simp only [arm64_norm, *])
    try dsimp only [execInst, execAddSubImm, execAddSubExt, execAddSubShift, execAddSubCarry, execLogicalImm,
      execLogicalShift, execMoveWide, execBitfield, execCondSelect, execCondCompare,
      execDataProc1, execDataProc2, execDataProc3, execLdr, execLdrLit, execStr, execLdp, execStp,
      evalLogical, evalBitfield, evalAddrMode, AddrMode.baseReg, checkRegSPAligned,
      checkAddrSPAligned, MemWidth.isAligned, State.spAligned, extendVal, Reg.fromZRBits,
      Reg.fromSPBits, State.readReg32]
    try simp (config := { decide := true }) only [arm64_norm, *]
    try arm64_discharge_perms_internal))

macro "kdf_reg" : tactic =>
  `(tactic| (
    try rw [State.readReg64_setMem]
    try rw [State.pc_setMem]
    try rw [State.sp_setMem]
    try rw [State.status_setMem]
    simp (config := { decide := true }) only [arm64_norm, *]))

section ExtractSegments

variable {b : BitVec 64} {C : Crypto} {ext : String → Option (State → State)}

set_option hygiene false in
local macro "hkdf_seg_e0_body" : tactic => `(tactic| (
  have hpc := hpre.pc_eq; have hrun := hpre.status
  have hx0 := hpre.x0_eq; have hx1 := hpre.x1_eq; have hx2 := hpre.x2_eq; have hx3 := hpre.x3_eq
  have hx4 := hpre.x4_eq; have hx5 := hpre.x5_eq; have hx6 := hpre.x6_eq; have hx7 := hpre.x7_eq
  have hsp_al := hpre.sp_aligned; have hhsp := hsp_aligned hpre.sp_aligned
  have hrw : s₀.mem.RW (hsp s₀) 688 := HFrame.rw_hsp hpre (Frame.refl s₀.mem _)
  iterate 18 kdf_step
  refine RunsTo.refl ?_
  refine ⟨by kdf_reg, ⟨by kdf_reg, by kdf_reg, by kdf_reg, ?_, ?_⟩,
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg⟩
  · simp only [Expand.mem_setMem]
    exact
      { m592 := by simp (config := { decide := true }) only [arm64_norm]
        m600 := by simp (config := { decide := true }) only [arm64_norm]
        m608 := by simp (config := { decide := true }) only [arm64_norm]
        m616 := by simp (config := { decide := true }) only [arm64_norm]
        m624 := by simp (config := { decide := true }) only [arm64_norm]
        m632 := by simp (config := { decide := true }) only [arm64_norm]
        m640 := by simp (config := { decide := true }) only [arm64_norm]
        m648 := by simp (config := { decide := true }) only [arm64_norm]
        m656 := by simp (config := { decide := true }) only [arm64_norm]
        m664 := by simp (config := { decide := true }) only [arm64_norm]
        m672 := by simp (config := { decide := true }) only [arm64_norm]
        m680 := by simp (config := { decide := true }) only [arm64_norm] }
  · exact HFrame.of_agreesOutside_hsp (off := 592#64) (sz := 96)
      (Frame.refl s₀.mem _) (by prove_agrees_hsp) (by decide)))

/-- Segment `E0` (`b + 0x5dda8` → `b + 0x61ac4`, 18 steps): prologue saving `x19..x30` at
`hsp s₀ + 592 .. 688`, setting `sp = hsp s₀`, `x29 = hsp s₀ + 592#64`, moving arguments into
`x22..x27`, and calling `new_from_slice(hsp s₀ + 32#64, saltA, salt.length)`. -/
theorem seg_e0_runsTo [HkdfHooks C.F ext] {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ : State}
    (hpre : HPre b salt ikm info saltA ikmA infoA okmA okmLen s₀) :
    RunsTo (tripleRatchetProgAtExt b ext) s₀
      (StateENfs1 b salt ikm info saltA ikmA infoA okmA okmLen s₀) := by
  hkdf_seg_e0_body

theorem seg_e0_placed_runsTo [LibsignalPlacement] {H : LibsignalHooks}
    {b_iv : BitVec 64} {aligned : Prop} {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s₀
      (StateENfs1 hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ · (lsmpl.base 402)) := by
  hkdf_seg_e0_body

/-- `new_from_slice` #1 (`pc_nfs` → `b + 0x5ddf0`): initializes
`Hmac(effectiveHmacKey C.F salt, [])` at `hsp s₀ + 40#64`. -/
theorem nfs1_runsTo {P : Program} {b_iv pc_nfs : BitVec 64} {aligned : Prop} {alignedM : Memory → Prop}
    (hNfs : Nfs3GenRunsToProg P b_iv pc_nfs alignedM C.F)
    {salt ikm info : List (BitVec 8)} {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ}
    {s₀ s : State}
    (hpre : HPre b salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (hx : StateENfs1 b salt ikm info saltA ikmA infoA okmA okmLen s₀ s pc_nfs)
    (hal : ∀ {m}, Expand.KeepsFrozenNoAnon s₀.mem m → alignedM m := by intro _; exact hpre.base_al) :
    RunsTo P s
      (StateERet1 b C.F salt ikm info ikmA infoA okmA okmLen s₀) := by
  have hx2_nat : (s.readReg64 .x2).toNat = salt.length := by
    rw [hx.x2_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hpre.salt_lt; omega)]
  have hrun := hNfs hx.pc_eq hx.common.status
    (by rw [hx2_nat]; exact hpre.salt_lt) (HFrame.ro_iv_bytes hpre hx.common.frame)
    (hal (HFrame.keepsFrozen hpre hx.common.frame)) (HFrame.ro_iv_read hpre hx.common.frame)
    (by rw [hx.common.sp_eq]; exact hpre.disj_iv_stk.sub_right (hsp s₀ - 544#64) ⟨by decide, by bv_omega⟩)
    (by rw [hx.x0_eq]; exact (HFrame.rw_hsp hpre hx.common.frame).sub (by bv_omega))
    (by rw [hx.common.sp_eq]; exact HFrame.rw_sub_544 hpre hx.common.frame)
    (by rw [hx.x0_eq, hx.common.sp_eq]; unfold DisjointRegions; bv_omega)
    (by rw [hx.x1_eq, hx2_nat, hx.common.sp_eq]
        exact hpre.disj_salt_stk.imp id (fun hd => hd.sub_right (hsp s₀ - 544#64) ⟨by decide, by bv_omega⟩))
    (by rw [hx.x1_eq, hx2_nat, hx.x0_eq]
        exact hpre.disj_salt_stk.imp id (fun hd => hd.sub_right (hsp s₀ + 32#64) ⟨by decide, by bv_omega⟩))
    (by rw [hx.common.sp_eq]; exact (hsp_aligned hpre.sp_aligned).2.1)
  refine hrun.mono fun s' ⟨hpc', hrun', hcs, htag, hhm, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'; rw [hx.x0_eq] at htag
  have hx0_8 : s.readReg64 .x0 + 8#64 = hsp s₀ + 40#64 := by rw [hx.x0_eq]; bv_lin
  have hsalt_s : s.mem.readBytes (s.readReg64 .x1) (s.readReg64 .x2).toNat = salt := by
    rw [hx.x1_eq, hx2_nat]; exact HFrame.salt_bytes hpre hx.common.frame
  rw [hx0_8, hsalt_s] at hhm; rw [hx.x0_eq, hx.common.sp_eq] at hfr
  exact ⟨hpc', HCommon.of_nfs_frame (retOff := 32#64) hx.common hrun' hcs hfr (by decide),
    (CalleeSaved.x22 hcs).trans hx.x22_eq, (CalleeSaved.x23 hcs).trans hx.x23_eq,
    (CalleeSaved.x24 hcs).trans hx.x24_eq, (CalleeSaved.x25 hcs).trans hx.x25_eq,
    (CalleeSaved.x26 hcs).trans hx.x26_eq, (CalleeSaved.x27 hcs).trans hx.x27_eq, htag, hhm⟩

theorem HmacStN.of_copy_19 {m₀ m : Memory} {src dst : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState} {key pfx tail : List (BitVec 8)}
    (hsrc : HmacStN m₀ src F key pfx tail)
    (h0   : m.read64 dst            = m₀.read64 src)
    (h8   : m.read64 (dst + 8#64)   = m₀.read64 (src + 8#64))
    (h16  : m.read64 (dst + 16#64)  = m₀.read64 (src + 16#64))
    (h24  : m.read64 (dst + 24#64)  = m₀.read64 (src + 24#64))
    (h32  : m.read64 (dst + 32#64)  = m₀.read64 (src + 32#64))
    (h40  : m.read64 (dst + 40#64)  = m₀.read64 (src + 40#64))
    (h48  : m.read64 (dst + 48#64)  = m₀.read64 (src + 48#64))
    (h56  : m.read64 (dst + 56#64)  = m₀.read64 (src + 56#64))
    (h64  : m.read64 (dst + 64#64)  = m₀.read64 (src + 64#64))
    (h72  : m.read64 (dst + 72#64)  = m₀.read64 (src + 72#64))
    (h80  : m.read64 (dst + 80#64)  = m₀.read64 (src + 80#64))
    (h88  : m.read64 (dst + 88#64)  = m₀.read64 (src + 88#64))
    (h96  : m.read64 (dst + 96#64)  = m₀.read64 (src + 96#64))
    (h104 : m.read64 (dst + 104#64) = m₀.read64 (src + 104#64))
    (h112 : m.read64 (dst + 112#64) = m₀.read64 (src + 112#64))
    (h120 : m.read64 (dst + 120#64) = m₀.read64 (src + 120#64))
    (h128 : m.read64 (dst + 128#64) = m₀.read64 (src + 128#64))
    (h136 : m.read64 (dst + 136#64) = m₀.read64 (src + 136#64)) :
    HmacStN m dst F key pfx tail := by
  rcases hsrc with ⟨hmod, hlen, hmsg, hpos, hin, hcnt1, hout, hcnt2⟩
  refine ⟨hmod, hlen, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h64_eq : m.readBytes dst 64 = m₀.readBytes src 64 := by
      rw [show (64 : ℕ) = 32 + 32 from rfl,
          Bytes.readBytes_add m dst 32 32, Bytes.readBytes_add m₀ src 32 32,
          readBytes_32_eq_of_read64_eq h0 h8 h16 h24,
          readBytes_32_eq_of_read64_eq h32 (by simpa [BitVec.add_assoc] using h40)
            (by simpa [BitVec.add_assoc] using h48) (by simpa [BitVec.add_assoc] using h56)]
    have hslice1 := Bytes.readBytes_slice_of_readBytes_eq m dst (m₀.readBytes src 64)
      (by rw [Memory.readBytes_length]; exact h64_eq) 0 tail.length (by rw [Memory.readBytes_length]; omega)
    have hslice2 := Bytes.readBytes_slice_of_readBytes_eq m₀ src (m₀.readBytes src 64)
      (by rw [Memory.readBytes_length]) 0 tail.length (by rw [Memory.readBytes_length]; omega)
    simpa [hmsg] using hslice1.trans hslice2.symm
  · have hd : dst + 0x3f#64 = (dst + 56#64) + 7#64 := by bv_lin
    have hs : src + 0x3f#64 = (src + 56#64) + 7#64 := by bv_lin
    rw [hd, read8_add_7_of_read64_eq h56, ← hs, hpos]
  · rw [readBytes_32_eq_of_read64_eq h64 (by simpa [BitVec.add_assoc] using h72)
          (by simpa [BitVec.add_assoc] using h80) (by simpa [BitVec.add_assoc] using h88), hin]
  · rw [show (0x60#64 : BitVec 64) = 96#64 from rfl, h96, ← hcnt1]
  · rw [readBytes_32_eq_of_read64_eq h104 (by simpa [BitVec.add_assoc] using h112)
          (by simpa [BitVec.add_assoc] using h120) (by simpa [BitVec.add_assoc] using h128), hout]
  · rw [show (0x88#64 : BitVec 64) = 136#64 from rfl, h136, ← hcnt2]

set_option hygiene false in
local macro "hkdf_seg_e1_lt56_body" b_code:term:max step_memcpy:term:max : tactic => `(tactic| (
  have hpc := hx.pc_eq; have hrun := hx.common.status; have hsp_eq := hx.common.sp_eq
  have hx29 := hx.common.x29_eq; have hx22 := hx.x22_eq; have hx23 := hx.x23_eq
  have hx24 := hx.x24_eq; have hx25 := hx.x25_eq; have hx26 := hx.x26_eq; have hx27 := hx.x27_eq
  have htag := hx.tag_32; have hhsp := hsp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (hsp s₀) 688 := HFrame.rw_hsp hpre hx.common.frame
  have hpos : s.mem.read8 (hsp s₀ + 103#64) = 0#8 := by
    have heq : hsp s₀ + 103#64 = (hsp s₀ + 40#64) + 0x3f#64 := by bv_lin
    rw [heq]; exact hx.hmac_40.2.2.1
  rcases Expand.cmp_lt64_lemmas hikm with ⟨h_ikm_ule, h_ikm_ult, h_ikm_cmp⟩
  iterate 29 kdf_step
  let m₀ := (((((((s.mem.write64 (hsp s₀ + 16#64) (BitVec.ofNat 64 info.length)).write64
        (hsp s₀ + 304#64) (s.mem.read64 (hsp s₀ + 136#64))).write64
        (hsp s₀ + 312#64) (s.mem.read64 (hsp s₀ + 144#64))).write64
        (hsp s₀ + 320#64) (s.mem.read64 (hsp s₀ + 152#64))).write64
        (hsp s₀ + 328#64) (s.mem.read64 (hsp s₀ + 160#64))).write64
        (hsp s₀ + 240#64) (s.mem.read64 (hsp s₀ + 72#64))).write64
        (hsp s₀ + 248#64) (s.mem.read64 (hsp s₀ + 80#64))
        |>.write64 (hsp s₀ + 256#64) (s.mem.read64 (hsp s₀ + 88#64))
        |>.write64 (hsp s₀ + 264#64) (s.mem.read64 (hsp s₀ + 96#64))
        |>.write64 (hsp s₀ + 336#64) (s.mem.read64 (hsp s₀ + 168#64))
        |>.write64 (hsp s₀ + 344#64) (s.mem.read64 (hsp s₀ + 176#64))
        |>.write64 (hsp s₀ + 208#64) (s.mem.read64 (hsp s₀ + 40#64))
        |>.write64 (hsp s₀ + 216#64) (s.mem.read64 (hsp s₀ + 48#64))
        |>.write64 (hsp s₀ + 224#64) (s.mem.read64 (hsp s₀ + 56#64))
        |>.write64 (hsp s₀ + 232#64) (s.mem.read64 (hsp s₀ + 64#64))
        |>.write64 (hsp s₀ + 272#64) (s.mem.read64 (hsp s₀ + 104#64))
        |>.write64 (hsp s₀ + 280#64) (s.mem.read64 (hsp s₀ + 112#64))
        |>.write64 (hsp s₀ + 288#64) (s.mem.read64 (hsp s₀ + 120#64))
        |>.write64 (hsp s₀ + 296#64) (s.mem.read64 (hsp s₀ + 128#64)))
  have hA0 : AgreesOutside s.mem m₀ (hsp s₀ + 16#64) 336 := by dsimp only [m₀]; prove_agrees_hsp
  have hc0 : HCommon okmLen s₀ (s.setMem m₀) :=
    HCommon.of_agreesOutside_hsp (off := 16#64) (sz := 336) hx.common hrun hsp_eq hx29 hA0 (by decide)
  have hhm0 : HmacSt m₀ (hsp s₀ + 208#64) C.F (effectiveHmacKey C.F salt) [] := by
    refine HmacSt.of_copy_empty hx.hmac_40 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp (config := { decide := true }) only [m₀, arm64_norm]
  have hm16_0 : m₀.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length := by
    simp (config := { decide := true }) only [m₀, arm64_norm]
  have hx2_nat : (BitVec.ofNat 64 ikm.length).toNat = ikm.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hikm_s : m₀.readBytes ikmA ikm.length = ikm := HFrame.ikm_bytes hpre hc0.frame
  have hrw_dst : m₀.RW (hsp s₀ + 208#64) ikm.length := (HFrame.rw_hsp hpre hc0.frame).sub (by bv_omega)
  refine $step_memcpy
    hrun rfl (by kdf_reg) (by kdf_reg) (by simp (config := { decide := true }) only [arm64_norm, *])
    ((by kdf_reg) : _ = $b_code + 0x5df48#64) hikm_s hrw_dst ?_
  let m₁ := m₀.writeBytes (hsp s₀ + 208#64) ikm
  have hA1 : AgreesOutside m₀ m₁ (hsp s₀ + 208#64) 63 :=
    Expand.agreesOutside_writeBytes_le m₀ (hsp s₀ + 208#64) ikm 63 (by omega)
  have hc1 : HCommon okmLen s₀ (s.setMem m₁) :=
    HCommon.of_agreesOutside_hsp (off := 208#64) (sz := 63) hc0 hrun hsp_eq hx29 hA1 (by decide)
  have hrw1 : m₁.RW (hsp s₀) 688 := HFrame.rw_hsp hpre hc1.frame
  dsimp only [m₁, m₀] at hrw1
  iterate 3 kdf_step
  refine RunsTo.refl ?_
  have hA2 : AgreesOutside m₁ (m₁.write8 (hsp s₀ + 271#64) (BitVec.ofNat 8 ikm.length)) (hsp s₀ + 271#64) 1 :=
    agreesOutside_hsp_write8 (AgreesOutside.rfl' m₁ (hsp s₀ + 271#64) 1) (by decide)
  refine ⟨by kdf_reg,
    HCommon.of_agreesOutside_hsp (off := 271#64) (sz := 1) hc1 (by kdf_reg) (by kdf_reg) (by kdf_reg) hA2 (by decide),
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, ?_, ?_⟩
  · show (m₁.write8 (hsp s₀ + 271#64) (BitVec.ofNat 8 ikm.length)).read64 (hsp s₀ + 16#64) =
      BitVec.ofNat 64 info.length
    rw [hA2.read64_eq (by unfold DisjointRegions; bv_omega),
        hA1.read64_eq (by unfold DisjointRegions; bv_omega)]
    exact hm16_0
  · refine ⟨[], ikm, rfl, by decide, hikm, ?_⟩
    have h271 : hsp s₀ + 271#64 = (hsp s₀ + 208#64) + 63#64 := by bv_lin
    show HmacStN (m₁.write8 (hsp s₀ + 271#64) (BitVec.ofNat 8 ikm.length))
      (hsp s₀ + 208#64) C.F (effectiveHmacKey C.F salt) [] ikm
    rw [h271]; exact HmacStN.of_hmacSt (HmacSt.of_writeBytes_lt63_write8_pos hhm0 hikm)))

theorem seg_e1_lt56_runsTo [HkdfHooks C.F ext] {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : HPre b salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hikm : ikm.length < 64)
    (hx : StateERet1 b C.F salt ikm info ikmA infoA okmA okmLen s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateE3cc b C.F salt ikm info infoA okmA okmLen s₀) := by
  hkdf_seg_e1_lt56_body b (s2_memcpy_step_ext b C ext)

theorem seg_e1_lt56_placed_runsTo [LibsignalPlacement] {H : LibsignalHooks}
    (h_memcpy : H lsMemcpySym = some memcpyHook)
    {b_iv : BitVec 64} {aligned : Prop} {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (hikm : ikm.length < 64)
    (hx : StateERet1 hkdfCodeFakeB C.F salt ikm info ikmA infoA okmA okmLen s₀ s) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s
      (StateE3cc hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen s₀) := by
  hkdf_seg_e1_lt56_body hkdfCodeFakeB (s2_memcpy_step_placed_429 h_memcpy)

set_option hygiene false in
local macro "hkdf_seg_e1_eq64_body" b_code:term:max step_comp_multi:term:max step_memcpy:term:max : tactic => `(tactic| (
  have hpc := hx.pc_eq; have hrun := hx.common.status; have hsp_eq := hx.common.sp_eq
  have hx29 := hx.common.x29_eq; have hx22 := hx.x22_eq; have hx23 := hx.x23_eq
  have hx24 := hx.x24_eq; have hx25 := hx.x25_eq; have hx26 := hx.x26_eq; have hx27 := hx.x27_eq
  have htag := hx.tag_32; have hhsp := hsp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (hsp s₀) 688 := HFrame.rw_hsp hpre hx.common.frame
  have hpos : s.mem.read8 (hsp s₀ + 103#64) = 0#8 := by
    have heq : hsp s₀ + 103#64 = (hsp s₀ + 40#64) + 0x3f#64 := by bv_lin
    rw [heq]; exact hx.hmac_40.2.2.1
  have hcnt_136 : s.mem.read64 (hsp s₀ + 136#64) = 1#64 := by
    have heq : hsp s₀ + 136#64 = (hsp s₀ + 40#64) + 0x60#64 := by bv_lin
    rw [heq]; exact hx.hmac_40.2.2.2.2.1
  rcases cmp_ge64_lemmas hikm hpre.ikm_len with ⟨h_ikm_ule, h_ikm_ult, h_ikm_cmp, h_ikm_cbz⟩
  iterate 35 kdf_step
  let m₁ := (((((((s.mem.write64 (hsp s₀ + 16#64) (BitVec.ofNat 64 info.length)).write64
        (hsp s₀ + 304#64) 1#64).write64
        (hsp s₀ + 312#64) (s.mem.read64 (hsp s₀ + 144#64))).write64
        (hsp s₀ + 320#64) (s.mem.read64 (hsp s₀ + 152#64))).write64
        (hsp s₀ + 328#64) (s.mem.read64 (hsp s₀ + 160#64))).write64
        (hsp s₀ + 240#64) (s.mem.read64 (hsp s₀ + 72#64))).write64
        (hsp s₀ + 248#64) (s.mem.read64 (hsp s₀ + 80#64))
        |>.write64 (hsp s₀ + 256#64) (s.mem.read64 (hsp s₀ + 88#64))
        |>.write64 (hsp s₀ + 264#64) (s.mem.read64 (hsp s₀ + 96#64))
        |>.write64 (hsp s₀ + 336#64) (s.mem.read64 (hsp s₀ + 168#64))
        |>.write64 (hsp s₀ + 344#64) (s.mem.read64 (hsp s₀ + 176#64))
        |>.write64 (hsp s₀ + 208#64) (s.mem.read64 (hsp s₀ + 40#64))
        |>.write64 (hsp s₀ + 216#64) (s.mem.read64 (hsp s₀ + 48#64))
        |>.write64 (hsp s₀ + 224#64) (s.mem.read64 (hsp s₀ + 56#64))
        |>.write64 (hsp s₀ + 232#64) (s.mem.read64 (hsp s₀ + 64#64))
        |>.write64 (hsp s₀ + 272#64) (s.mem.read64 (hsp s₀ + 104#64))
        |>.write64 (hsp s₀ + 280#64) (s.mem.read64 (hsp s₀ + 112#64))
        |>.write64 (hsp s₀ + 288#64) (s.mem.read64 (hsp s₀ + 120#64))
        |>.write64 (hsp s₀ + 296#64) (s.mem.read64 (hsp s₀ + 128#64))
        |>.write64 (hsp s₀ + 304#64) (1#64 + (BitVec.ofNat 64 ikm.length >>> 6)))
  have hA1 : AgreesOutside s.mem m₁ (hsp s₀ + 16#64) 336 := by dsimp only [m₁]; prove_agrees_hsp
  have hc1 : HCommon okmLen s₀ (s.setMem m₁) :=
    HCommon.of_agreesOutside_hsp (off := 16#64) (sz := 336) hx.common hrun hsp_eq hx29 hA1 (by decide)
  have hist_272 : m₁.readBytes (hsp s₀ + 272#64) 32 = shaStateBytes (hmacInnerInit C.F (effectiveHmacKey C.F salt)) := by
    have h40 : s.mem.readBytes (hsp s₀ + 104#64) 32 = shaStateBytes (hmacInnerInit C.F (effectiveHmacKey C.F salt)) := by
      have heq : hsp s₀ + 104#64 = (hsp s₀ + 40#64) + 0x40#64 := by bv_lin
      rw [heq]; exact hx.hmac_40.2.2.2.1
    rw [readBytes_32_eq_of_read64_eq (m₂ := s.mem) (a₁ := hsp s₀ + 272#64) (a₂ := hsp s₀ + 104#64)
          (by simp (config := { decide := true }) only [m₁, arm64_norm])
          (by simp (config := { decide := true }) only [m₁, arm64_norm])
          (by simp (config := { decide := true }) only [m₁, arm64_norm])
          (by simp (config := { decide := true }) only [m₁, arm64_norm]), h40]
  obtain ⟨nBlocks, hnBlocks⟩ : ∃ nBlocks, ikm.length / 64 = nBlocks := ⟨_, rfl⟩
  obtain ⟨pfx, hpfx_def⟩ : ∃ pfx, ikm.take (64 * nBlocks) = pfx := ⟨_, rfl⟩
  obtain ⟨tail, htail_def⟩ : ∃ tail, ikm.drop (64 * nBlocks) = tail := ⟨_, rfl⟩
  obtain ⟨st', hst'_def⟩ : ∃ st', (chunks64 pfx).foldl C.F (hmacInnerInit C.F (effectiveHmacKey C.F salt)) = st' := ⟨_, rfl⟩
  have hpfx_len : pfx.length = 64 * nBlocks := by rw [← hpfx_def, List.length_take]; omega
  have htail_len : tail.length = ikm.length - 64 * nBlocks := by rw [← htail_def, List.length_drop]
  have htail_lt : tail.length < 64 := by rw [htail_len, ← hnBlocks]; omega
  have hpfx_m1 : m₁.readBytes ikmA (64 * nBlocks) = pfx := by
    have hikm_all : m₁.readBytes ikmA ikm.length = ikm := HFrame.ikm_bytes hpre hc1.frame
    simpa [hpfx_def] using Bytes.readBytes_slice_of_readBytes_eq m₁ ikmA ikm hikm_all 0 (64 * nBlocks) (by omega)
  have hrw_272 : m₁.RW (hsp s₀ + 272#64) 32 := (HFrame.rw_hsp hpre hc1.frame).sub (by bv_omega)
  refine $step_comp_multi
    hrun rfl (by kdf_reg) (by kdf_reg)
    (by have h1 := (ikm_split_lemmas hpre.ikm_len).1; simp (config := { decide := true }) only [arm64_norm, *])
    ((by kdf_reg) : _ = $b_code + 0x5dfbc#64) hist_272 hpfx_m1 hst'_def hrw_272 ?_
  let m₂ := m₁.writeBytes (hsp s₀ + 272#64) (shaStateBytes st')
  have hA2 : AgreesOutside m₁ m₂ (hsp s₀ + 272#64) 32 :=
    Expand.agreesOutside_writeBytes_le m₁ (hsp s₀ + 272#64) (shaStateBytes st') 32 (by simp)
  have hc2 : HCommon okmLen s₀ (s.setMem m₂) :=
    HCommon.of_agreesOutside_hsp (off := 272#64) (sz := 32) hc1 hrun hsp_eq hx29 hA2 (by decide)
  have hrw2 : m₂.RW (hsp s₀) 688 := HFrame.rw_hsp hpre hc2.frame
  dsimp only [m₂, m₁] at hrw2
  iterate 5 kdf_step
  let m₃ := m₂.write8 (hsp s₀ + 271#64) (BitVec.truncate 8 (BitVec.ofNat 64 ikm.length &&& 63#64))
  have hA3 : AgreesOutside m₂ m₃ (hsp s₀ + 271#64) 1 :=
    agreesOutside_hsp_write8 (AgreesOutside.rfl' m₂ (hsp s₀ + 271#64) 1) (by decide)
  have hc3 : HCommon okmLen s₀ (s.setMem m₃) :=
    HCommon.of_agreesOutside_hsp (off := 271#64) (sz := 1) hc2 hrun hsp_eq hx29 hA3 (by decide)
  have htail_m3 : m₃.readBytes (ikmA + (BitVec.ofNat 64 ikm.length &&& 9223372036854775744#64)) tail.length = tail := by
    have hikm_all : m₃.readBytes ikmA ikm.length = ikm := HFrame.ikm_bytes hpre hc3.frame
    have hslice := Bytes.readBytes_slice_of_readBytes_eq m₃ ikmA ikm hikm_all (64 * nBlocks) tail.length (by omega)
    rw [(ikm_split_lemmas hpre.ikm_len).2.2.1, hnBlocks]
    have htake : List.take tail.length (List.drop (64 * nBlocks) ikm) = tail := by rw [htail_def, List.take_length]
    simpa [htake] using hslice
  have hrw_tail : m₃.RW (hsp s₀ + 208#64) tail.length := (HFrame.rw_hsp hpre hc3.frame).sub (by bv_omega)
  refine $step_memcpy
    hrun rfl (by kdf_reg) (by kdf_reg)
    (by have h4 := (ikm_split_lemmas hpre.ikm_len).2.2.2.1; simp (config := { decide := true }) only [arm64_norm, *])
    ((by kdf_reg) : _ = $b_code + 0x5dfd0#64) htail_m3 hrw_tail ?_
  let m₄ := m₃.writeBytes (hsp s₀ + 208#64) tail
  have hA4 : AgreesOutside m₃ m₄ (hsp s₀ + 208#64) 63 :=
    Expand.agreesOutside_writeBytes_le m₃ (hsp s₀ + 208#64) tail 63 (by omega)
  have hc4 : HCommon okmLen s₀ (s.setMem m₄) :=
    HCommon.of_agreesOutside_hsp (off := 208#64) (sz := 63) hc3 hrun hsp_eq hx29 hA4 (by decide)
  have hrw4 : m₄.RW (hsp s₀) 688 := HFrame.rw_hsp hpre hc4.frame
  have hm16_2 : m₂.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length := by
    rw [hA2.read64_eq (by unfold DisjointRegions; bv_omega)]; simp (config := { decide := true }) only [m₁, arm64_norm]
  have hm16_3 : m₃.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length := by
    rw [hA3.read64_eq (by unfold DisjointRegions; bv_omega)]; exact hm16_2
  have hm16_4 : m₄.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length := by
    rw [hA4.read64_eq (by unfold DisjointRegions; bv_omega)]; exact hm16_3
  have hm16_4_raw := hm16_4
  dsimp only [m₄, m₃, m₂, m₁] at hrw4 hm16_4_raw
  iterate 1 kdf_step
  rcases ikm_split_lemmas hpre.ikm_len with ⟨h_shr_nat, h_cnt_add, h_and_hi, h_and_lo_nat, h_and_lo_tr8⟩
  refine RunsTo.refl ?_
  refine ⟨by kdf_reg, ⟨by kdf_reg, by kdf_reg, by kdf_reg,
    by rw [Expand.mem_setMem]; exact hc4.saved, by rw [Expand.mem_setMem]; exact hc4.frame⟩,
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    by rw [Expand.mem_setMem]; exact hm16_4, ?_⟩
  rw [Expand.mem_setMem]
  have hikm_app : pfx ++ tail = ikm := by rw [← hpfx_def, ← htail_def, List.take_append_drop]
  refine ⟨pfx, tail, hikm_app, by omega, htail_lt, by omega, htail_lt, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Bytes.readBytes_writeBytes_same m₃ (hsp s₀ + 208#64) tail (by omega)
  · have h271 : (hsp s₀ + 208#64) + 0x3f#64 = hsp s₀ + 271#64 := by bv_lin
    have hout : OutsideRegion (hsp s₀ + 208#64) 63 (hsp s₀ + 271#64) := by simp only [OutsideRegion]; bv_omega
    rw [h271, hA4.1 _ hout, Memory.read8_write8_same, h_and_lo_tr8, hnBlocks, ← htail_len]
  · have h272 : (hsp s₀ + 208#64) + 0x40#64 = hsp s₀ + 272#64 := by bv_lin
    rw [h272, hA4.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        hA3.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide), hst'_def]
    have hlen : (shaStateBytes st').length = 32 := shaStateBytes_length _
    conv_lhs => rw [← hlen]
    exact Bytes.readBytes_writeBytes_same m₁ (hsp s₀ + 272#64) (shaStateBytes st') (by rw [hlen]; decide)
  · have h304 : (hsp s₀ + 208#64) + 0x60#64 = hsp s₀ + 304#64 := by bv_lin
    rw [h304, hA4.read64_eq (by unfold DisjointRegions; bv_omega),
        hA3.read64_eq (by unfold DisjointRegions; bv_omega),
        hA2.read64_eq (by unfold DisjointRegions; bv_omega)]
    have hm1_304 : m₁.read64 (hsp s₀ + 304#64) = 1#64 + (BitVec.ofNat 64 ikm.length >>> 6) := by
      simp (config := { decide := true }) only [m₁, arm64_norm]
    have hpfx_div : pfx.length / 64 = nBlocks := by omega
    rw [hm1_304, h_cnt_add, hnBlocks, hpfx_div]
  · have h312 : (hsp s₀ + 208#64) + 0x68#64 = hsp s₀ + 312#64 := by bv_lin
    rw [h312, hA4.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        hA3.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        hA2.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        readBytes_32_eq_of_read64_eq (m₂ := s.mem) (a₁ := hsp s₀ + 312#64) (a₂ := (hsp s₀ + 40#64) + 0x68#64)
          (by simp (config := { decide := true }) only [m₁, arm64_norm])
          (by simp (config := { decide := true }) only [m₁, arm64_norm])
          (by simp (config := { decide := true }) only [m₁, arm64_norm])
          (by simp (config := { decide := true }) only [m₁, arm64_norm])]
    exact hx.hmac_40.2.2.2.2.2.1
  · have h344 : (hsp s₀ + 208#64) + 0x88#64 = hsp s₀ + 344#64 := by bv_lin
    have h176 : hsp s₀ + 176#64 = (hsp s₀ + 40#64) + 0x88#64 := by bv_lin
    rw [h344, hA4.read64_eq (by unfold DisjointRegions; bv_omega),
        hA3.read64_eq (by unfold DisjointRegions; bv_omega),
        hA2.read64_eq (by unfold DisjointRegions; bv_omega)]
    have hm1_344 : m₁.read64 (hsp s₀ + 344#64) = s.mem.read64 (hsp s₀ + 176#64) := by
      simp (config := { decide := true }) only [m₁, arm64_norm]
    rw [hm1_344, h176]; exact hx.hmac_40.2.2.2.2.2.2))

set_option maxHeartbeats 800000 in
theorem seg_e1_eq64_runsTo [HkdfHooks C.F ext] {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : HPre b salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hikm : 64 ≤ ikm.length)
    (hx : StateERet1 b C.F salt ikm info ikmA infoA okmA okmLen s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateE3cc b C.F salt ikm info infoA okmA okmLen s₀) := by
  hkdf_seg_e1_eq64_body b (s2_compress256_multi_step_ext b C ext) (s2_memcpy_step_ext b C ext)

set_option maxHeartbeats 800000 in
theorem seg_e1_eq64_placed_runsTo [LibsignalPlacement] {H : LibsignalHooks}
    (h_memcpy : H lsMemcpySym = some memcpyHook)
    (h_compress : H lsCompress256Sym = some (compress256Hook C.F))
    {b_iv : BitVec 64} {aligned : Prop} {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (hikm : 64 ≤ ikm.length)
    (hx : StateERet1 hkdfCodeFakeB C.F salt ikm info ikmA infoA okmA okmLen s₀ s) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s
      (StateE3cc hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen s₀) := by
  hkdf_seg_e1_eq64_body hkdfCodeFakeB
    (s2_compress256_multi_step_placed_429 h_compress) (s2_memcpy_step_placed_429 h_memcpy)

/-- Segment `E1` (`b + 0x632cc` → `b + 0x633cc`): feeds `ikm` (`< 2 ^ 63` bytes) into `Hmac`. -/
theorem seg_e1_runsTo [HkdfHooks C.F ext] {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : HPre b salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hx : StateERet1 b C.F salt ikm info ikmA infoA okmA okmLen s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateE3cc b C.F salt ikm info infoA okmA okmLen s₀) := by
  by_cases hikm : ikm.length < 64
  · exact seg_e1_lt56_runsTo hpre hikm hx
  · exact seg_e1_eq64_runsTo hpre (by omega) hx

theorem seg_e1_placed_runsTo [LibsignalPlacement] {H : LibsignalHooks}
    (h_memcpy : H lsMemcpySym = some memcpyHook)
    (h_compress : H lsCompress256Sym = some (compress256Hook C.F))
    {b_iv : BitVec 64} {aligned : Prop} {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (hx : StateERet1 hkdfCodeFakeB C.F salt ikm info ikmA infoA okmA okmLen s₀ s) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s
      (StateE3cc hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen s₀) := by
  by_cases hikm : ikm.length < 64
  · exact seg_e1_lt56_placed_runsTo h_memcpy hpre hikm hx
  · exact seg_e1_eq64_placed_runsTo h_memcpy h_compress hpre (by omega) hx

end ExtractSegments

end HkdfToSliceProof

end CryptoVerification.SpqrV1.Kdf
