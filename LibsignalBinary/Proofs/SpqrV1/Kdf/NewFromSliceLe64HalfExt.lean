/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants
public import LibsignalBinary.Proofs.SpqrV1.Kdf.FrameROExt
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.EntryAndKeyBlock
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceFirstHalf
import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceFirstHalf
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon
import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSlice -- shake: keep

/-!
# Contract-Backed First Half of `Hmac<Sha256>::new_from_slice [local#3]`

Contract-backed straight-line segments (`0x66fa0 → 0x6748c`) for the `key.length ≤ 64` prologue,
`memcpy`, and ipad XOR chunks of `new_from_slice [local#3]`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.SpqrV1.Kdf.Nfs3Ext

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.CBC
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister memcpyHook memsetHook toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open CryptoVerification.LibsignalSession.CryptoHmacSha256
open CryptoVerification.LibsignalSessionRepr
open Obj
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetProgAtExt extHookStack)
open CryptoVerification.LibsignalTripleRatchet.Extract (RunsToE S2Frame)
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Kdf.SpqrKdfExt
open CryptoVerification.SpqrV1.Kdf.NewFromSlice3Proof hiding
  NfsMemInv3 NfsRegInv3
  read64_write8_stack_iv write64_quad_400_iv write64_quad_0_ivsw
  Nfs3OpadPostHook Nfs3OpadMidState Nfs3OpadEndState
  Nfs3PreCompress2 Nfs3PostCompress2 rodata_sha256IV_0x837d8
open ProofLib.ProgramReflection
open CryptoVerification.CodeLayout

attribute [-arm64_norm, -simp] CryptoVerification.SpqrV1.Kdf.NewFromSlice3Proof.read64_write8_stack_iv

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm]
  MemWidth.bytes SimdMemSize.bytes
  Memory.read8_write8_base_off_disjoint
  Memory.read8_write8_base_zero_off
  Memory.read8_write8_base_off_zero
  Memory.read8_write64_base_off_disjoint
  Memory.read8_write64_base_zero_off
  Memory.read8_write64_base_off_zero
  Memory.read8_write64_base_off_inbounds
  Memory.read64_write64_base_off_disjoint
  Memory.read64_write64_base_zero_off
  Memory.read64_write64_base_off_zero
  Memory.read64_write8_base_off_disjoint
  Memory.read64_write8_base_zero_off
  Memory.read64_write8_base_off_zero
  truncate8_zeroExtend_xor_32
  truncate8_zeroExtend_xor_64

/-! ## `RunsToE` / `S2Frame` / `S2FrameRO` Stack-Frame Bridge Lemmas (`extHookStack = 16384`) -/

theorem RunsToE.of_hmacRunsTo {prog : Program} {s₀ : State} {P : State → Prop}
    (h : RunsTo prog s₀ P) : RunsToE prog s₀ P := by
  intro hL
  obtain ⟨sf, hst, htr, hvregs, hP, hLf⟩ := h hL
  exact ⟨sf, hst, ⟨htr, hvregs⟩, hP, hLf⟩

theorem S2Frame.readBytes_eq_of_readable {m₁ m₂ : Memory} {regs : List (BitVec 64 × ℕ)}
    (h : S2Frame m₁ m₂ regs) {a : BitVec 64} {n : ℕ} (hread : m₁.Readable a n)
    (hd : ∀ r ∈ regs, DisjointRegions r.1 r.2 a n) (hn : n ≤ 2 ^ 64 := by decide) :
    m₂.readBytes a n = m₁.readBytes a n := by
  refine Memory.readBytes_congr_region hn fun b hb => ?_
  exact h.1 b (hread b hb).1 (hread b hb).2 fun r hr_mem => (hd r hr_mem).outside hb hn

theorem s2Frame_of_r7b_frame_16928 {out sp : BitVec 64} {m₁ m₂ : Memory}
    (hf : Frame m₁ m₂ [(out, 0x98), (sp - 544#64, 544)]) :
    S2Frame m₁ m₂ [(out, 0x98), (sp - 16928#64, 16928)] := by
  refine (S2Frame.of_frame hf).mono fun a ha r hr => ?_
  have hout := ha (out, 0x98) (by simp)
  have hstk := ha (sp - 16928#64, 16928) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hout
  · clear * - hstk
    simp only [OutsideRegion] at hstk ⊢
    bv_omega

theorem s2Frame_of_r7b_stack_frame_16928 {out sp : BitVec 64} {m₁ m₂ : Memory}
    (hf : Frame m₁ m₂ [(sp - 544#64, 544)]) :
    S2Frame m₁ m₂ [(out, 0x98), (sp - 16928#64, 16928)] := by
  refine (S2Frame.of_frame hf).mono fun a ha r hr => ?_
  have hstk := ha (sp - 16928#64, 16928) (by simp)
  simp only [List.mem_singleton] at hr
  subst hr
  clear * - hstk
  simp only [OutsideRegion] at hstk ⊢
  bv_omega

theorem s2Frame_of_hook_frame_16928 {out sp nfsSp_sp off : BitVec 64} {sz : ℕ} {m₁ m₂ : Memory}
    (hf : S2Frame m₁ m₂ [(nfsSp_sp + off, sz), (nfsSp_sp - BitVec.ofNat 64 extHookStack, extHookStack)])
    (hsp : nfsSp_sp = sp - 544#64)
    (hoff : off.toNat + sz ≤ 544) :
    S2Frame m₁ m₂ [(out, 0x98), (sp - 16928#64, 16928)] := by
  subst hsp
  refine hf.mono fun a ha r hr => ?_
  have hstk := ha (sp - 16928#64, 16928) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · clear * - hstk hoff
    simp only [OutsideRegion] at hstk ⊢
    bv_omega
  · clear * - hstk
    simp only [OutsideRegion, extHookStack] at hstk ⊢
    bv_omega

theorem s2FrameRO_of_hook_frame_16928 {roRegs : List (BitVec 64 × ℕ)}
    {out sp nfsSp_sp off : BitVec 64} {sz : ℕ} {m₁ m₂ : Memory}
    (hf : S2FrameRO roRegs m₁ m₂ [(nfsSp_sp + off, sz), (nfsSp_sp - BitVec.ofNat 64 extHookStack, extHookStack)])
    (hsp : nfsSp_sp = sp - 544#64)
    (hoff : off.toNat + sz ≤ 544) :
    S2FrameRO roRegs m₁ m₂ [(out, 0x98), (sp - 16928#64, 16928)] := by
  subst hsp
  refine hf.mono fun a ha r hr => ?_
  have hstk := ha (sp - 16928#64, 16928) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · clear * - hstk hoff
    simp only [OutsideRegion] at hstk ⊢
    bv_omega
  · clear * - hstk
    simp only [OutsideRegion, extHookStack] at hstk ⊢
    bv_omega

theorem s2Frame_hook_readBytes_stack_eq {sp off k : BitVec 64} {sz n : ℕ} {m m' : Memory}
    (hf : S2Frame m m' [(sp + off, sz), (sp - BitVec.ofNat 64 extHookStack, extHookStack)])
    (hrw_stk : m.RW sp 544)
    (hd_stk_ext : DisjointRegions sp 544 (sp - 16384#64) 16384)
    (hk : 0 < n ∧ k.toNat + n ≤ 544)
    (hd_off_k : sz ≤ (k - off).toNat ∧ n ≤ (off - k).toNat) :
    m'.readBytes (sp + k) n = m.readBytes (sp + k) n := by
  have hrw_k : RW m (sp + k) n := hrw_stk.sub (by have := hk.2; clear * - this; bv_omega)
  refine hf.readBytes_eq hrw_k (fun r hr => ?_) (by have := hk.2; omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rcases hd_off_k with ⟨h1, h2⟩
    clear * - h1 h2
    simp only [DisjointRegions]
    bv_omega
  · exact (hd_stk_ext.sub_left (sp + k) ⟨hk.1, by have := hk.2; clear * - this; bv_omega⟩).symm

theorem s2FrameRO_hook_read64_stack_eq {roRegs : List (BitVec 64 × ℕ)}
    {sp off k : BitVec 64} {sz : ℕ} {m m' : Memory}
    (hf : S2FrameRO roRegs m m' [(sp + off, sz), (sp - BitVec.ofNat 64 extHookStack, extHookStack)])
    (hrw_stk : m.RW sp 544)
    (hd_stk_ext : DisjointRegions sp 544 (sp - 16384#64) 16384)
    (hk : k.toNat + 8 ≤ 544)
    (hd_off_k : sz = 0 ∨ (sz ≤ (k - off).toNat ∧ 8 ≤ (off - k).toNat)) :
    m'.read64 (sp + k) = m.read64 (sp + k) := by
  have hrw_k : RW m (sp + k) 8 := hrw_stk.sub (by clear * - hk; bv_omega)
  refine Memory.read64_congr fun b hb => ?_
  obtain ⟨hperm_b, hlf_b⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (hrw_k b hb)
  have hr : (m.perm b).r = true := by rw [hperm_b]; rfl
  refine hf.1 b hr hlf_b fun r hr_mem => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem
  rcases hr_mem with rfl | rfl
  · rcases hd_off_k with rfl | ⟨h1, h2⟩
    · simp [OutsideRegion]
    · have hd : DisjointRegions (sp + off) sz (sp + k) 8 := by
        clear * - h1 h2; simp only [DisjointRegions]; bv_omega
      exact hd.outside hb (by decide)
  · exact (hd_stk_ext.sub_left (sp + k) ⟨by decide, by clear * - hk; bv_omega⟩).symm.outside hb (by decide)

theorem s2Frame_hook_read64_stack_eq {sp off k : BitVec 64} {sz : ℕ} {m m' : Memory}
    (hf : S2Frame m m' [(sp + off, sz), (sp - BitVec.ofNat 64 extHookStack, extHookStack)])
    (hrw_stk : m.RW sp 544)
    (hd_stk_ext : DisjointRegions sp 544 (sp - 16384#64) 16384)
    (hk : k.toNat + 8 ≤ 544)
    (hd_off_k : sz = 0 ∨ (sz ≤ (k - off).toNat ∧ 8 ≤ (off - k).toNat)) :
    m'.read64 (sp + k) = m.read64 (sp + k) :=
  s2FrameRO_hook_read64_stack_eq (S2FrameRO.of_s2frame (roRegs := []) hf) hrw_stk hd_stk_ext hk hd_off_k

theorem nfsSavedStack_setMem_iff {s₀ : State} {m₁ m : Memory} :
    NfsSavedStack (s₀.setMem m₁) m ↔ NfsSavedStack s₀ m := by
  constructor <;> intro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ <;>
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem frame_of_agreesOutside_stack_only {sp : BitVec 64} {m₀ m m' : Memory}
    {off : BitVec 64} {sz : ℕ}
    (hf : Frame m₀ m [(sp, 544)])
    (hA : AgreesOutside m m' (sp + off) sz)
    (hoff : off.toNat + sz ≤ 544) :
    Frame m₀ m' [(sp, 544)] :=
  hf.trans_agreesOutside_sub (b := sp) (n := 544) (by simp) (by clear * - hoff; bv_omega) hA

theorem NfsSavedStack.of_s2Frame_low {s₀ : State} {m m' : Memory}
    {off : BitVec 64} {sz : ℕ}
    (hs : NfsSavedStack s₀ m)
    (hrw_stk : m.RW (nfsSp s₀) 544)
    (hd_stk_ext : DisjointRegions (nfsSp s₀) 544 (nfsSp s₀ - 16384#64) 16384)
    (hf : S2Frame m m' [(nfsSp s₀ + off, sz), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)])
    (hoff : off.toNat + sz ≤ 432) :
    NfsSavedStack s₀ m' := by
  have hread (k : BitVec 64) (hk : 432 ≤ k.toNat ∧ k.toNat + 8 ≤ 544) :
      m'.read64 (nfsSp s₀ + k) = m.read64 (nfsSp s₀ + k) :=
    s2Frame_hook_read64_stack_eq hf hrw_stk hd_stk_ext hk.2
      (by
        by_cases hsz : sz = 0
        · exact Or.inl hsz
        · refine Or.inr ?_
          rcases hk with ⟨h1, h2⟩
          clear * - hsz hoff h1 h2
          constructor <;> bv_omega)
  exact {
    m432 := (hread 432#64 (by decide)).trans hs.m432
    m464 := (hread 464#64 (by decide)).trans hs.m464
    m472 := (hread 472#64 (by decide)).trans hs.m472
    m480 := (hread 480#64 (by decide)).trans hs.m480
    m496 := (hread 496#64 (by decide)).trans hs.m496
    m504 := (hread 504#64 (by decide)).trans hs.m504
    m512 := (hread 512#64 (by decide)).trans hs.m512
    m520 := (hread 520#64 (by decide)).trans hs.m520
    m528 := (hread 528#64 (by decide)).trans hs.m528
    m536 := (hread 536#64 (by decide)).trans hs.m536
  }

/-! ## Instruction Decodes & First-Half Invariants -/

@[local simp, local arm64_norm]
theorem adrp_newFromSlice3_mask :
    (bv% (ls_off% newFromSlice3Name + 40) &&& 0xfffffffffffff000#64 : BitVec 64) =
      bv% (page% (ls_off% newFromSlice3Name + 40)) := rfl

@[local simp, local arm64_norm] private
gen_decodes libsignalSessionCode_tree libsignalSessionCode [(ls_off% newFromSlice3Name) → (ls_off% newFromSlice3Name + 1264)]

macro "nfs3x_step" : tactic =>
  `(tactic| (
    refine RunsTo.step (inst := ?inst) ?hrun ?hfetch ?_
    case hfetch => (
      (try simp (config := { decide := true }) only [arm64_norm, *])
      refine libsignalSessionCode_fetch_rebase_text ?_ (by decide) (by decide)
      (try simp only [arm64_norm]) <;> rfl)
    case hrun => (simp only [arm64_norm, *])
    try dsimp only [execInst, execAddSubImm, execAddSubExt, execAddSubShift, execAddSubCarry, execLogicalImm,
      execLogicalShift, execMoveWide, execBitfield, execCondSelect, execCondCompare,
      execDataProc1, execDataProc1, execDataProc2, execDataProc3, execLdr, execLdrLit, execStr, execLdp, execStp,
      evalLogical, evalBitfield, evalAddrMode, AddrMode.baseReg, checkRegSPAligned,
      checkAddrSPAligned, MemWidth.isAligned, State.spAligned, extendVal, Reg.fromZRBits,
      Reg.fromSPBits]
    try simp (config := { decide := true }) only [arm64_norm, *]
    try arm64_discharge_perms_internal))

theorem nfs3_adrp_x22 {b : BitVec 64} (hb : (b &&& 0xfff#64) = 0#64) :
    ((b + bv% (ls_off% newFromSlice3Name + 40)) &&& 0xfffffffffffff000#64) +
      bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44) - page% (ls_off% newFromSlice3Name + 40)) =
      b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44)) := by
  bv_bits

theorem nfs3_adrp_x22_assoc {b : BitVec 64} (hb : (b &&& 0xfff#64) = 0#64) :
    (((b + bv% (ls_off% newFromSlice3Name + 40)) &&& 0xfffffffffffff000#64) +
      bv% (page% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44)) - page% (ls_off% newFromSlice3Name + 40))) +
      bv% ((ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44)) % 4096) =
      b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44)) := by
  bv_bits

structure NfsMemInv3 (b : BitVec 64) (s₀ : State) (m : Memory) : Prop where
  rw_stack : m.RW (nfsSp s₀) 544
  rw_out : m.RW (s₀.readReg64 .x0) 0x98
  readable_iv : m.Readable (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32
  iv_bytes : m.readBytes (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 = shaStateBytes sha256IV
  disj_iv_stack : DisjointRegions (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 (nfsSp s₀) 544
  disj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (nfsSp s₀) 544
  saved : NfsSavedStack s₀ m
  frame : Frame s₀.mem m [(s₀.readReg64 .x0, 0x98), (nfsSp s₀, 544)]

structure NfsRegInv3 (b : BitVec 64) (s₀ s : State) : Prop where
  sp_eq : s.sp = nfsSp s₀
  sp_align : (nfsSp s₀ &&& 0b1111#64) = 0#64
  x29_eq : s.readReg64 .x29 = nfsSp s₀ + 464#64
  x19_eq : s.readReg64 .x19 = s₀.readReg64 .x0
  x20_eq : s.readReg64 .x20 = 1#64
  x22_eq : s.readReg64 .x22 = b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))
  x25_eq : s.readReg64 .x25 = s₀.readReg64 .x25
  x26_eq : s.readReg64 .x26 = s₀.readReg64 .x26
  x27_eq : s.readReg64 .x27 = s₀.readReg64 .x27

theorem NfsMemInv3.of_agreesOutside_low {b : BitVec 64} {s₀ : State} {m m' : Memory}
    {off : BitVec 64} {sz : ℕ}
    (hM : NfsMemInv3 b s₀ m)
    (hA : AgreesOutside m m' (nfsSp s₀ + off) sz)
    (hoff : 0 < sz ∧ off.toNat + sz ≤ 432) :
    NfsMemInv3 b s₀ m' := by
  have hf := agreesOutside_toFrame hA
  have hdisj_iv : DisjointRegions (nfsSp s₀ + off) sz (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 := by
    refine hM.disj_iv_stack.symm.sub_left (nfsSp s₀ + off) ⟨hoff.1, ?_⟩
    rcases hoff with ⟨_, _⟩
    bv_omega
  exact {
    rw_stack := (Frame.rw_iff hf _ _).mpr hM.rw_stack
    rw_out := (Frame.rw_iff hf _ _).mpr hM.rw_out
    readable_iv := (Frame.readable_iff hf _ _).mpr hM.readable_iv
    iv_bytes := (Frame.readBytes_eq hf (by simp [hdisj_iv]) (by decide)).trans hM.iv_bytes
    disj_iv_stack := hM.disj_iv_stack
    disj_out_stack := hM.disj_out_stack
    saved := hM.saved.of_agreesOutside_low hA hoff
    frame := Frame.of_agreesOutside_stack hM.frame hA (by omega)
  }

theorem NfsMemInv3.writeBytes_low {b : BitVec 64} {s₀ : State} {m : Memory}
    (hM : NfsMemInv3 b s₀ m) (off : BitVec 64) (bs : List (BitVec 8))
    (hoff : 0 < bs.length ∧ off.toNat + bs.length ≤ 432) :
    NfsMemInv3 b s₀ (m.writeBytes (nfsSp s₀ + off) bs) :=
  hM.of_agreesOutside_low (ProofLib.agreesOutside_writeBytes m (nfsSp s₀ + off) bs) hoff

theorem NfsMemInv3.write64_low {b : BitVec 64} {s₀ : State} {m : Memory}
    (hM : NfsMemInv3 b s₀ m) (off : BitVec 64) (v : BitVec 64)
    (hoff : off.toNat + 8 ≤ 432 := by decide) :
    NfsMemInv3 b s₀ (m.write64 (nfsSp s₀ + off) v) :=
  hM.of_agreesOutside_low (AgreesOutside.write64_self m (nfsSp s₀ + off) v) ⟨by decide, hoff⟩

theorem NfsMemInv3.write128_low {b : BitVec 64} {s₀ : State} {m : Memory}
    (hM : NfsMemInv3 b s₀ m) (off : BitVec 64) (v : BitVec 128)
    (hoff : off.toNat + 16 ≤ 432 := by decide) :
    NfsMemInv3 b s₀ (m.write128 (nfsSp s₀ + off) v) :=
  hM.of_agreesOutside_low (AgreesOutside.write128_self m (nfsSp s₀ + off) v) ⟨by decide, hoff⟩

theorem NfsMemInv3.writeBytes_zero {b : BitVec 64} {s₀ : State} {m : Memory}
    (hM : NfsMemInv3 b s₀ m) (bs : List (BitVec 8))
    (hbs : 0 < bs.length ∧ bs.length ≤ 432) :
    NfsMemInv3 b s₀ (m.writeBytes (nfsSp s₀) bs) := by
  rw [← BitVec.add_zero (nfsSp s₀)]
  exact hM.writeBytes_low 0#64 bs (by simpa using hbs)

@[local simp, local arm64_norm]
theorem read64_write8_stack_iv {b : BitVec 64} {s₀ : State}
    (hdisj : DisjointRegions (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 (nfsSp s₀) 544)
    (m : Memory) (off c : BitVec 64) (v : BitVec 8)
    (hc : decide (c.toNat < 544) = true)
    (hoff : decide (num% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44)) ≤ off.toNat ∧ off.toNat + 8 ≤ num% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44) + 32)) = true) :
    (m.write8 (nfsSp s₀ + c) v).read64 (b + off) = m.read64 (b + off) := by
  have hc' : c.toNat < 544 := of_decide_eq_true hc
  have ⟨hoff1, hoff2⟩ : num% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44)) ≤ off.toNat ∧ off.toNat + 8 ≤ num% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44) + 32) := of_decide_eq_true hoff
  refine Frame.read64_eq (agreesOutside_toFrame (AgreesOutside.write8_self m (nfsSp s₀ + c) v)) ?_
  clear * - hdisj hc' hoff1 hoff2
  simp only [List.mem_singleton, forall_eq, DisjointRegions] at hdisj ⊢
  bv_omega

theorem write64_quad_400_iv (b : BitVec 64) (m₁ m₂ : Memory) (sp : BitVec 64)
    (hiv : m₂.readBytes (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 = shaStateBytes sha256IV) :
    ((((m₁.write64 (sp + 400#64) (m₂.read64 (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))))).write64
      (sp + 408#64) (m₂.read64 (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44) + 8)))).write64
      (sp + 416#64) (m₂.read64 (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44) + 16)))).write64
      (sp + 424#64) (m₂.read64 (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44) + 24)))) =
    m₁.writeBytes (sp + 400#64) (shaStateBytes sha256IV) := by
  have hd1 : sp + 408#64 = (sp + 400#64) + 8#64 := by bv_omega
  have hd2 : sp + 416#64 = (sp + 400#64) + 16#64 := by bv_omega
  have hd3 : sp + 424#64 = (sp + 400#64) + 24#64 := by bv_omega
  have hs1 : b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44) + 8) = (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) + 8#64 := by bv_omega
  have hs2 : b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44) + 16) = (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) + 16#64 := by bv_omega
  have hs3 : b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44) + 24) = (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) + 24#64 := by bv_omega
  rw [hd1, hd2, hd3, hs1, hs2, hs3, write64_quad_read64_eq_writeBytes_32, hiv]

theorem write64_quad_0_ivsw (b : BitVec 64) (m₁ m₂ : Memory) (sp : BitVec 64)
    (hiv : m₂.readBytes (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 = shaStateBytes sha256IV) :
    ((((m₁.write64 sp (m₂.read64 (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44) + 16)))).write64
      (sp + 8#64) (m₂.read64 (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44) + 24)))).write64
      (sp + 16#64) (m₂.read64 (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))))).write64
      (sp + 24#64) (m₂.read64 (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44) + 8)))) =
    m₁.writeBytes sp ((shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) := by
  have hd3 : sp + 24#64 = (sp + 16#64) + 8#64 := by bv_omega
  have hs1 : b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44) + 24) = (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44) + 16)) + 8#64 := by bv_omega
  have hs2 : b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44) + 8) = (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) + 8#64 := by bv_omega
  have hlen : (shaStateBytes sha256IV).length = 32 := shaStateBytes_length sha256IV
  have htake : m₂.readBytes (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 16 = (shaStateBytes sha256IV).take 16 := by
    have h := readBytes_slice_of_readBytes_eq m₂ (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) (shaStateBytes sha256IV)
      (by rw [hlen]; exact hiv) 0 16 (by omega)
    simpa using h
  have hdrop : m₂.readBytes (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44) + 16)) 16 = (shaStateBytes sha256IV).drop 16 := by
    have h := readBytes_slice_of_readBytes_eq m₂ (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) (shaStateBytes sha256IV)
      (by rw [hlen]; exact hiv) 16 16 (by omega)
    have hadd : (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) + BitVec.ofNat 64 16 = b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44) + 16) := by bv_omega
    rw [hadd, List.take_of_length_le (by simp [hlen])] at h
    exact h
  rw [hd3, hs1, hs2, write64_pair_read64_eq_writeBytes_16, write64_pair_read64_eq_writeBytes_16,
      hdrop, htake, writeBytes_append]
  have hlen_drop : ((shaStateBytes sha256IV).drop 16).length = 16 := by simp [hlen]
  rw [hlen_drop]

theorem write64_quad_240_iv (b : BitVec 64) (m₁ m₂ : Memory) (sp : BitVec 64)
    (hiv : m₂.readBytes (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 = shaStateBytes sha256IV) :
    ((((m₁.write64 (sp + 240#64) (m₂.read64 (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))))).write64
      (sp + 248#64) (m₂.read64 (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44) + 8)))).write64
      (sp + 256#64) (m₂.read64 (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44) + 16)))).write64
      (sp + 264#64) (m₂.read64 (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44) + 24)))) =
    m₁.writeBytes (sp + 240#64) (shaStateBytes sha256IV) := by
  have hd1 : sp + 248#64 = (sp + 240#64) + 8#64 := by bv_omega
  have hd2 : sp + 256#64 = (sp + 240#64) + 16#64 := by bv_omega
  have hd3 : sp + 264#64 = (sp + 240#64) + 24#64 := by bv_omega
  have hs1 : b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44) + 8) = (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) + 8#64 := by bv_omega
  have hs2 : b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44) + 16) = (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) + 16#64 := by bv_omega
  have hs3 : b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44) + 24) = (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) + 24#64 := by bv_omega
  rw [hd1, hd2, hd3, hs1, hs2, hs3, write64_quad_read64_eq_writeBytes_32, hiv]

theorem NfsRegInv3.setMem_iff {b : BitVec 64} {s₀ s : State} {m₁ : Memory} :
    NfsRegInv3 b (s₀.setMem m₁) s ↔ NfsRegInv3 b s₀ s := by
  constructor <;> intro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ <;>
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem nfsRegInv3_of_cc {b : BitVec 64} {s₀ s s' : State}
    (hR : NfsRegInv3 b s₀ s) (hcc : CallingConventionPreserved s s') :
    NfsRegInv3 b s₀ s' :=
  ⟨hcc.1.trans hR.sp_eq,
   hR.sp_align,
   hcc.2.2.2.2.2.2.2.2.2.2.2.1.trans hR.x29_eq,
   hcc.2.1.trans hR.x19_eq,
   hcc.2.2.1.trans hR.x20_eq,
   hcc.2.2.2.2.1.trans hR.x22_eq,
   hcc.2.2.2.2.2.2.2.1.trans hR.x25_eq,
   hcc.2.2.2.2.2.2.2.2.1.trans hR.x26_eq,
   hcc.2.2.2.2.2.2.2.2.2.1.trans hR.x27_eq⟩

theorem NfsMemInv3.of_s2Frame_low {b : BitVec 64} {s₀ : State} {m₀ m m' : Memory}
    {off : BitVec 64} {sz : ℕ}
    (hM : NfsMemInv3 b (s₀.setMem m₀) m)
    (hd_stk_ext : DisjointRegions (nfsSp s₀) 544 (nfsSp s₀ - 16384#64) 16384)
    (hd_iv_ext : DisjointRegions (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 (nfsSp s₀ - 16384#64) 16384)
    (hf : S2Frame m m' [(nfsSp s₀ + off, sz), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)])
    (hoff : 0 < sz ∧ off.toNat + sz ≤ 432) :
    NfsMemInv3 b (s₀.setMem m') m' := by
  have hrw_stk : m.RW (nfsSp s₀) 544 := hM.rw_stack
  have hrw_out : m.RW (s₀.readReg64 .x0) 0x98 := hM.rw_out
  have hdisj_iv : DisjointRegions (nfsSp s₀ + off) sz (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 := by
    have hd_iv_stk : DisjointRegions (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 (nfsSp s₀) 544 := hM.disj_iv_stack
    refine hd_iv_stk.symm.sub_left (nfsSp s₀ + off) ⟨hoff.1, ?_⟩
    have := hoff.2
    clear * - this
    bv_omega
  exact {
    rw_stack := hf.rw_of_rw _ _ hrw_stk
    rw_out := hf.rw_of_rw _ _ hrw_out
    readable_iv := SpqrKdfExt.S2Frame.readable_of_readable hf hM.readable_iv
    iv_bytes := (S2Frame.readBytes_eq_of_readable hf hM.readable_iv (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hdisj_iv
      · exact hd_iv_ext.symm) (by decide)).trans hM.iv_bytes
    disj_iv_stack := hM.disj_iv_stack
    disj_out_stack := hM.disj_out_stack
    saved := nfsSavedStack_setMem_iff.mpr
      (NfsSavedStack.of_s2Frame_low (nfsSavedStack_setMem_iff.mp hM.saved) hrw_stk hd_stk_ext hf hoff.2)
    frame := Frame.refl m' _
  }

/-! ## First-Half Straight-Line Segments (`hex:66fa0 → hex:6748c`) -/

set_option maxHeartbeats 1600000 in
/-- First 17 instructions of `new_from_slice [local#3]` (`hex:66fa0 → memcpy`). -/
theorem nfs3_seg0a_ext {b : BitVec 64} {ext : String → Option (State → State)} {s₀ : State}
    (hpc : s₀.pc = b + bv% (ls_off% newFromSlice3Name))
    (hstat : s₀.status = .Running)
    (hlen : (s₀.readReg64 .x2).toNat ≤ 64)
    (hb : (b &&& 0xfff#64) = 0#64)
    (hrw_stack : s₀.mem.RW (s₀.sp - 544#64) 544)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    RunsTo (tripleRatchetProgAtExt b ext) s₀ (fun s1 =>
      s1.pc = b + bv% (ls_off% "memcpy") ∧
      s1.status = .Running ∧
      s1.sp = nfsSp s₀ ∧
      (nfsSp s₀ &&& 0b1111#64) = 0#64 ∧
      s1.readReg64 .x29 = nfsSp s₀ + 464#64 ∧
      s1.readReg64 .x19 = s₀.readReg64 .x0 ∧
      s1.readReg64 .x22 = b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44)) ∧
      s1.readReg64 .x25 = s₀.readReg64 .x25 ∧
      s1.readReg64 .x26 = s₀.readReg64 .x26 ∧
      s1.readReg64 .x27 = s₀.readReg64 .x27 ∧
      s1.readReg64 .x0 = nfsSp s₀ + 112#64 ∧
      s1.readReg64 .x1 = s₀.readReg64 .x1 ∧
      s1.readReg64 .x2 = s₀.readReg64 .x2 ∧
      s1.readReg64 .lr = b + bv% (ls_off% newFromSlice3Name + 68) ∧
      s1.mem.readBytes (nfsSp s₀ + 112#64) 64 = List.replicate 64 0#8 ∧
      NfsSavedStack s₀ (s1.mem.write64 (nfsSp s₀ + 432#64) 1#64) ∧
      Frame s₀.mem s1.mem [(nfsSp s₀, 544)]) := by
  generalize hPost : (fun s1 : State => _) = Post
  have hsp₀ : s₀.sp = nfsSp s₀ + 544#64 := nfs_sp_eq_add s₀
  have hal_nfs : (nfsSp s₀ &&& 0b1111#64) = 0#64 := nfs_sp_align hal
  have hal_464 : ((nfsSp s₀ + 464#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_464_align hal
  have hal_544 : ((nfsSp s₀ + 544#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_544_align hal
  have hRW_stack : s₀.mem.RW (nfsSp s₀) 544 := hrw_stack
  have hcond : BitVec.ule 0x41#64 (s₀.readReg64 .x2) = false := nfs_ule_65_false hlen
  have hadrp1 := nfs3_adrp_x22_assoc hb
  have hadrp2 := nfs3_adrp_x22 hb
  iterate 17 nfs3x_step
  subst hPost
  refine RunsTo.refl ?_
  have hA_pro : AgreesOutside s₀.mem (nfsPrologueMem s₀) (nfsSp s₀ + 464#64) 80 :=
    agreesOutside_nfsPrologueMem s₀
  have hA_zero : AgreesOutside (nfsPrologueMem s₀)
      ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8))
      (nfsSp s₀ + 112#64) 64 := by
    simpa using ProofLib.agreesOutside_writeBytes (nfsPrologueMem s₀) (nfsSp s₀ + 112#64) (List.replicate 64 0#8)
  have hoct :
      ((((((((nfsPrologueMem s₀).write64 (nfsSp s₀ + 112#64) 0#64).write64
        (nfsSp s₀ + 120#64) 0#64).write64 (nfsSp s₀ + 128#64) 0#64).write64
        (nfsSp s₀ + 136#64) 0#64).write64 (nfsSp s₀ + 144#64) 0#64).write64
        (nfsSp s₀ + 152#64) 0#64).write64 (nfsSp s₀ + 160#64) 0#64).write64
        (nfsSp s₀ + 168#64) 0#64 =
      (nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8) :=
    write64_oct_zero_eq_writeBytes_64 (nfsPrologueMem s₀) (nfsSp s₀)
  dsimp only [nfsPrologueMem, Reg.x29, Reg.x30, Reg.x28, Reg.x24, Reg.x23,
    Reg.x22, Reg.x21, Reg.x20, Reg.x19] at hoct
  refine ⟨by simp only [arm64_norm], by simp only [arm64_norm, hstat],
    by simp only [arm64_norm], hal_nfs, by simp only [arm64_norm],
    by simp only [arm64_norm], by simp only [arm64_norm, hadrp1, hadrp2]; try bv_bits,
    by simp only [arm64_norm], by simp only [arm64_norm],
    by simp only [arm64_norm], by simp only [arm64_norm],
    by simp only [arm64_norm], by simp only [arm64_norm],
    by simp only [arm64_norm], ?_, ?_, ?_⟩
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC, State.setPC]
    rw [hoct]
    exact Layout.readBytes_writeBytes_eq (nfsPrologueMem s₀) (nfsSp s₀ + 112#64)
      (List.replicate 64 0#8) 64 (by simp) (by decide)
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC, State.setPC]
    rw [hoct]
    exact nfsSavedStack_prologue_432 s₀ _ hA_zero
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC, State.setPC]
    rw [hoct]
    exact frame_of_agreesOutside_stack_only
      (frame_of_agreesOutside_stack_only (Frame.refl s₀.mem _) hA_pro (by decide))
      hA_zero (by decide)

set_option maxHeartbeats 1600000 in
/-- Next 10 instructions after `memcpy` returns (`hex:66fe4 → hex:6717c`). -/
theorem nfs3_seg0b_ext {b : BitVec 64} {ext : String → Option (State → State)}
    {s₀ s : State} {key : List (BitVec 8)}
    (hlen : key.length ≤ 64)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64)
    (hpc : s.pc = b + bv% (ls_off% newFromSlice3Name + 68))
    (hstat : s.status = .Running)
    (hsp : s.sp = nfsSp s₀)
    (hsp_align : (nfsSp s₀ &&& 0b1111#64) = 0#64)
    (hx29 : s.readReg64 .x29 = nfsSp s₀ + 464#64)
    (hx19 : s.readReg64 .x19 = s₀.readReg64 .x0)
    (hx22 : s.readReg64 .x22 = b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44)))
    (hx25 : s.readReg64 .x25 = s₀.readReg64 .x25)
    (hx26 : s.readReg64 .x26 = s₀.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s₀.readReg64 .x27)
    (hM_432 : NfsMemInv3 b (s₀.setMem s.mem) (s.mem.write64 (nfsSp s₀ + 432#64) 1#64))
    (hk0_64 : s.mem.readBytes (nfsSp s₀ + 112#64) 64 = keyBlock key) :
    RunsTo (tripleRatchetProgAtExt b ext) s (fun s' =>
      s'.pc = b + bv% (ls_off% newFromSlice3Name + 476) ∧
      s'.status = .Running ∧
      NfsRegInv3 b s₀ s' ∧
      NfsMemInv3 b (s₀.setMem s.mem) s'.mem ∧
      s'.readReg64 .x8 = 0x36#64 ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧
      s'.readReg64 .x2 = 1#64 ∧
      s'.readVReg128 2#5 = s'.mem.read64 (nfsSp s₀ + 152#64) ++ s'.mem.read64 (nfsSp s₀ + 144#64) ∧
      s'.readVReg128 0#5 = s'.mem.read64 (nfsSp s₀ + 168#64) ++ s'.mem.read64 (nfsSp s₀ + 160#64) ∧
      s'.mem.readBytes (nfsSp s₀ + 144#64) 32 = (keyBlock key).drop 32 ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 (keyBlock key) 0 ∧
      s'.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 (keyBlock key) 16) := by
  generalize hPost : (fun s' : State => _) = Post
  have hal_464 : ((nfsSp s₀ + 464#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_464_align hal
  have hkb_len : (keyBlock key).length = 64 := keyBlock_length hlen
  have hA_432 : AgreesOutside s.mem (s.mem.write64 (nfsSp s₀ + 432#64) 1#64) (nfsSp s₀ + 432#64) 8 :=
    AgreesOutside.write64_self s.mem (nfsSp s₀ + 432#64) 1#64
  have hRW_low : s.mem.RW (nfsSp s₀) 432 := by
    intro a ha
    have hout : OutsideRegion (nfsSp s₀ + 432#64) 8 a := by
      clear * - ha; unfold InRegion OutsideRegion at *; bv_omega
    have ha544 : InRegion (nfsSp (s₀.setMem s.mem)) 544 a := by
      clear * - ha; dsimp only [InRegion, nfsSp, State.setMem] at *; omega
    have h432 := Memory.permNoLazy_eq_some_rw_iff.mp (hM_432.rw_stack a ha544)
    exact Memory.permNoLazy_eq_some_rw_iff.mpr
      ⟨(congrFun hA_432.2.1 a).symm.trans h432.1, (hA_432.2.2.1 a hout).symm.trans h432.2⟩
  have hcw_432 : s.mem.canWrite (nfsSp s₀ + 432#64) 8 = true := by
    rw [Memory.canWrite_congr hA_432.2.1.symm]
    exact hM_432.rw_stack.canWrite_sub (by clear * -; dsimp [nfsSp, State.setMem]; bv_omega) (by decide)
  iterate 10 nfs3x_step
  subst hPost
  refine RunsTo.refl ?_
  set m_k0 := s.mem
  have hk0_take32 : m_k0.readBytes (nfsSp s₀ + 112#64) 32 = (keyBlock key).take 32 := by
    have h := readBytes_slice_of_readBytes_eq m_k0 (nfsSp s₀ + 112#64) (keyBlock key)
      (by rw [hkb_len]; exact hk0_64) 0 32 (by omega)
    simpa using h
  have hk0_drop32 : m_k0.readBytes (nfsSp s₀ + 144#64) 32 = (keyBlock key).drop 32 := by
    have h := readBytes_slice_of_readBytes_eq m_k0 (nfsSp s₀ + 112#64) (keyBlock key)
      (by rw [hkb_len]; exact hk0_64) 32 32 (by omega)
    have hadd : (nfsSp s₀ + 112#64) + BitVec.ofNat 64 32 = nfsSp s₀ + 144#64 := by clear * -; bv_omega
    rw [hadd, List.take_of_length_le (by simp [hkb_len])] at h
    exact h
  have hM_final : NfsMemInv3 b (s₀.setMem s.mem)
      (((m_k0.write64 (nfsSp s₀ + 432#64) 1#64).writeBytes
        (nfsSp s₀ + 288#64) (slice16 (keyBlock key) 0)).writeBytes
        (nfsSp s₀ + 304#64) (slice16 (keyBlock key) 16)) :=
    (hM_432.writeBytes_low 288#64 _ (by simp [slice16_length])).writeBytes_low
      304#64 _ (by simp [slice16_length])
  have h144_eq :
      (((m_k0.write64 (nfsSp s₀ + 432#64) 1#64).writeBytes
        (nfsSp s₀ + 288#64) (slice16 (keyBlock key) 0)).writeBytes
        (nfsSp s₀ + 304#64) (slice16 (keyBlock key) 16)).readBytes (nfsSp s₀ + 144#64) 32 =
      (keyBlock key).drop 32 := by
    rw [readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _),
        readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _),
        (agreesOutside_toFrame hA_432).readBytes_eq
          (by clear * -; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega) (by decide),
        hk0_drop32]
  refine ⟨by simp only [arm64_norm, hpc], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm, hsp], hsp_align, by simp only [arm64_norm, hx29],
     by simp only [arm64_norm, hx19], by simp only [arm64_norm],
     by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx25],
     by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27]⟩,
    ?_,
    by simp only [arm64_norm], by simp only [arm64_norm, hsp],
    by simp only [arm64_norm, hsp], by simp only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm, hsp],
    by simp (config := { decide := true }) only [arm64_norm, hsp],
    ?_, ?_, ?_⟩
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact hM_final
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact h144_eq
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans
      (readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _))
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _)

set_option maxHeartbeats 1600000 in
theorem nfs3_chunk1_ext {b : BitVec 64} {ext : String → Option (State → State)}
    {s₀ s : State} {key : List (BitVec 8)}
    (hlen : key.length ≤ 64)
    (hpc : s.pc = b + bv% (ls_off% newFromSlice3Name + 476))
    (hstat : s.status = .Running)
    (hR : NfsRegInv3 b s₀ s)
    (hM : NfsMemInv3 b s₀ s.mem)
    (hx8 : s.readReg64 .x8 = 0x36#64)
    (hx0 : s.readReg64 .x0 = nfsSp s₀ + 400#64)
    (hx1 : s.readReg64 .x1 = nfsSp s₀ + 288#64)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hs0 : s.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 (keyBlock key) 0)
    (hs16 : s.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 (keyBlock key) 16) :
    RunsTo (tripleRatchetProgAtExt b ext) s (fun s' =>
      s'.pc = b + bv% (ls_off% newFromSlice3Name + 676) ∧
      s'.status = .Running ∧
      NfsRegInv3 b s₀ s' ∧
      NfsMemInv3 b s₀ s'.mem ∧
      s'.readReg64 .x8 = 0x36#64 ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧
      s'.readReg64 .x2 = 1#64 ∧
      s'.readReg64 .x10 = (byteAt (keyBlock key) 16).zeroExtend 64 ∧
      s'.readReg64 .x11 = (byteAt (keyBlock key) 17).zeroExtend 64 ∧
      s'.readVReg128 2#5 = s.readVReg128 2#5 ∧
      s'.readVReg128 0#5 = s.readVReg128 0#5 ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 0 ∧
      s'.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 (keyBlock key) 16) := by
  generalize hPost : (fun s' : State => _) = Post
  obtain ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩ := hR
  have hRW_stack : s.mem.RW (nfsSp s₀) 544 := hM.rw_stack
  obtain ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7,
          hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15⟩ :=
    read8_16_of_readBytes_slice16 s.mem (nfsSp s₀) 288#64 (keyBlock key) 0 hs0
  obtain ⟨hb16, hb17, -⟩ :=
    read8_16_of_readBytes_slice16 s.mem (nfsSp s₀) 304#64 (keyBlock key) 16 hs16
  simp only [Nat.add_zero, Nat.reduceAdd, BitVec.reduceAdd] at hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14 hb15 hb16 hb17
  iterate 50 nfs3x_step
  subst hPost
  refine RunsTo.refl ?_
  refine ⟨by simp only [arm64_norm, hpc], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm, hsp], hsp_align, by simp only [arm64_norm, hx29],
     by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
     by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx25],
     by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27]⟩,
    ?_,
    by simp only [arm64_norm, hx8], by simp only [arm64_norm, hx0],
    by simp only [arm64_norm, hx1], by simp only [arm64_norm, hx2],
    by simp only [arm64_norm], by simp only [arm64_norm],
    by simp only [arm64_norm], by simp only [arm64_norm],
    ?_, ?_⟩
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write8_16_stack_288_xor _ _ _ _ (keyBlock_length hlen)]
    exact hM.writeBytes_low 288#64 _ (by simp [slice16_length])
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write8_16_stack_288_xor _ _ _ _ (keyBlock_length hlen)]
    exact readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _)
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write8_16_stack_288_xor _ _ _ _ (keyBlock_length hlen)]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans hs16

set_option maxHeartbeats 1600000 in
theorem nfs3_chunk2_ext {b : BitVec 64} {ext : String → Option (State → State)}
    {s₀ s : State} {m_k0 : Memory} {key : List (BitVec 8)}
    (hlen : key.length ≤ 64)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64)
    (hpc : s.pc = b + bv% (ls_off% newFromSlice3Name + 676))
    (hstat : s.status = .Running)
    (hR : NfsRegInv3 b s₀ s)
    (hM : NfsMemInv3 b s₀ s.mem)
    (hx8 : s.readReg64 .x8 = 0x36#64)
    (hx0 : s.readReg64 .x0 = nfsSp s₀ + 400#64)
    (hx1 : s.readReg64 .x1 = nfsSp s₀ + 288#64)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hx10 : s.readReg64 .x10 = (byteAt (keyBlock key) 16).zeroExtend 64)
    (hx11 : s.readReg64 .x11 = (byteAt (keyBlock key) 17).zeroExtend 64)
    (hq2 : s.readVReg128 2#5 = m_k0.read64 (nfsSp s₀ + 152#64) ++ m_k0.read64 (nfsSp s₀ + 144#64))
    (hq0 : s.readVReg128 0#5 = m_k0.read64 (nfsSp s₀ + 168#64) ++ m_k0.read64 (nfsSp s₀ + 160#64))
    (hk0_drop32 : m_k0.readBytes (nfsSp s₀ + 144#64) 32 = (keyBlock key).drop 32)
    (hs0 : s.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 0)
    (hs16 : s.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 (keyBlock key) 16) :
    RunsTo (tripleRatchetProgAtExt b ext) s (fun s' =>
      s'.pc = b + bv% (ls_off% newFromSlice3Name + 876) ∧
      s'.status = .Running ∧
      NfsRegInv3 b s₀ s' ∧
      NfsMemInv3 b s₀ s'.mem ∧
      s'.readReg64 .x8 = 0x36#64 ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧
      s'.readReg64 .x2 = 1#64 ∧
      s'.readReg64 .x11 = (byteAt (keyBlock key) 32 ^^^ 0x36#8).zeroExtend 64 ∧
      s'.readReg64 .x9 = (byteAt (keyBlock key) 33).zeroExtend 64 ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 0 ∧
      s'.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 16 ∧
      s'.mem.readBytes (nfsSp s₀ + 320#64) 16 = slice16 (keyBlock key) 32 ∧
      s'.mem.readBytes (nfsSp s₀ + 336#64) 16 = slice16 (keyBlock key) 48) := by
  generalize hPost : (fun s' : State => _) = Post
  obtain ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩ := hR
  have hRW_stack : s.mem.RW (nfsSp s₀) 544 := hM.rw_stack
  have hal_464 : ((nfsSp s₀ + 464#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_464_align hal
  have hkb_len : (keyBlock key).length = 64 := keyBlock_length hlen
  obtain ⟨hb16, hb17, hb18, hb19, hb20, hb21, hb22, hb23,
          hb24, hb25, hb26, hb27, hb28, hb29, hb30, hb31⟩ :=
    read8_16_of_readBytes_slice16 s.mem (nfsSp s₀) 304#64 (keyBlock key) 16 hs16
  obtain ⟨hb32, hb33, -⟩ :=
    read8_16_of_readBytes_slice16 m_k0 (nfsSp s₀) 144#64 (keyBlock key) 32
      (readBytes_16_of_drop_32 m_k0 (nfsSp s₀) (keyBlock key) hkb_len hk0_drop32)
  simp only [Nat.add_zero, Nat.reduceAdd, BitVec.reduceAdd] at hb16 hb17 hb18 hb19 hb20 hb21 hb22 hb23 hb24 hb25 hb26 hb27 hb28 hb29 hb30 hb31 hb32 hb33
  iterate 50 nfs3x_step
  subst hPost
  refine RunsTo.refl ?_
  have hM_final : NfsMemInv3 b s₀
      (((s.mem.writeBytes (nfsSp s₀ + 304#64) (slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 16)).writeBytes
        (nfsSp s₀ + 320#64) (slice16 (keyBlock key) 32)).writeBytes
        (nfsSp s₀ + 336#64) (slice16 (keyBlock key) 48)) :=
    (((hM.writeBytes_low 304#64 _ (by simp [slice16_length])).writeBytes_low
      320#64 _ (by simp [slice16_length])).writeBytes_low
      336#64 _ (by simp [slice16_length]))
  refine ⟨by simp only [arm64_norm, hpc], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm, hsp], hsp_align, by simp only [arm64_norm, hx29],
     by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
     by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx25],
     by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27]⟩,
    ?_,
    by simp only [arm64_norm, hx8], by simp only [arm64_norm, hx0],
    by simp only [arm64_norm, hx1], by simp only [arm64_norm, hx2],
    by simp only [arm64_norm], by simp only [arm64_norm],
    ?_, ?_, ?_, ?_⟩
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_320_eq_writeBytes_slice16 _ m_k0 (nfsSp s₀) (keyBlock key) hkb_len hk0_drop32]
    simp (config := { decide := true }) only [writeBytes_slice16_write8_comm]
    rw [write8_16_stack_304_xor _ _ _ _ hkb_len]
    exact hM_final
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_320_eq_writeBytes_slice16 _ m_k0 (nfsSp s₀) (keyBlock key) hkb_len hk0_drop32]
    simp (config := { decide := true }) only [writeBytes_slice16_write8_comm]
    rw [write8_16_stack_304_xor _ _ _ _ hkb_len]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans
      ((readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans
        ((readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans hs0))
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_320_eq_writeBytes_slice16 _ m_k0 (nfsSp s₀) (keyBlock key) hkb_len hk0_drop32]
    simp (config := { decide := true }) only [writeBytes_slice16_write8_comm]
    rw [write8_16_stack_304_xor _ _ _ _ hkb_len]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans
      ((readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans
        (readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _)))
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_320_eq_writeBytes_slice16 _ m_k0 (nfsSp s₀) (keyBlock key) hkb_len hk0_drop32]
    simp (config := { decide := true }) only [writeBytes_slice16_write8_comm]
    rw [write8_16_stack_304_xor _ _ _ _ hkb_len]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans
      (readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _))
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_320_eq_writeBytes_slice16 _ m_k0 (nfsSp s₀) (keyBlock key) hkb_len hk0_drop32]
    simp (config := { decide := true }) only [writeBytes_slice16_write8_comm]
    rw [write8_16_stack_304_xor _ _ _ _ hkb_len]
    exact readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _)

set_option maxHeartbeats 1600000 in
theorem nfs3_chunk3_ext {b : BitVec 64} {ext : String → Option (State → State)}
    {s₀ s : State} {key : List (BitVec 8)}
    (hlen : key.length ≤ 64)
    (hpc : s.pc = b + bv% (ls_off% newFromSlice3Name + 876))
    (hstat : s.status = .Running)
    (hR : NfsRegInv3 b s₀ s)
    (hM : NfsMemInv3 b s₀ s.mem)
    (hx8 : s.readReg64 .x8 = 0x36#64)
    (hx0 : s.readReg64 .x0 = nfsSp s₀ + 400#64)
    (hx1 : s.readReg64 .x1 = nfsSp s₀ + 288#64)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hx11 : s.readReg64 .x11 = (byteAt (keyBlock key) 32 ^^^ 0x36#8).zeroExtend 64)
    (hx9 : s.readReg64 .x9 = (byteAt (keyBlock key) 33).zeroExtend 64)
    (hs0 : s.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 0)
    (hs16 : s.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 16)
    (hs32 : s.mem.readBytes (nfsSp s₀ + 320#64) 16 = slice16 (keyBlock key) 32)
    (hs48 : s.mem.readBytes (nfsSp s₀ + 336#64) 16 = slice16 (keyBlock key) 48) :
    RunsTo (tripleRatchetProgAtExt b ext) s (fun s' =>
      s'.pc = b + bv% (ls_off% newFromSlice3Name + 1068) ∧
      s'.status = .Running ∧
      NfsRegInv3 b s₀ s' ∧
      NfsMemInv3 b s₀ s'.mem ∧
      s'.readReg64 .x8 = 0x36#64 ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧
      s'.readReg64 .x2 = 1#64 ∧
      s'.readReg64 .x9 = (byteAt (keyBlock key) 48 ^^^ 0x36#8).zeroExtend 64 ∧
      s'.readReg64 .x10 = (byteAt (keyBlock key) 49).zeroExtend 64 ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 0 ∧
      s'.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 16 ∧
      s'.mem.readBytes (nfsSp s₀ + 320#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 32 ∧
      s'.mem.readBytes (nfsSp s₀ + 336#64) 16 = slice16 (keyBlock key) 48) := by
  generalize hPost : (fun s' : State => _) = Post
  obtain ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩ := hR
  have hRW_stack : s.mem.RW (nfsSp s₀) 544 := hM.rw_stack
  have hkb_len : (keyBlock key).length = 64 := keyBlock_length hlen
  obtain ⟨-, -, hb34, hb35, hb36, hb37, hb38, hb39,
          hb40, hb41, hb42, hb43, hb44, hb45, hb46, hb47⟩ :=
    read8_16_of_readBytes_slice16 s.mem (nfsSp s₀) 320#64 (keyBlock key) 32 hs32
  obtain ⟨hb48, hb49, -⟩ :=
    read8_16_of_readBytes_slice16 s.mem (nfsSp s₀) 336#64 (keyBlock key) 48 hs48
  simp only [Nat.add_zero, Nat.reduceAdd, BitVec.reduceAdd] at hb34 hb35 hb36 hb37 hb38 hb39 hb40 hb41 hb42 hb43 hb44 hb45 hb46 hb47 hb48 hb49
  iterate 48 nfs3x_step
  subst hPost
  refine RunsTo.refl ?_
  refine ⟨by simp only [arm64_norm, hpc], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm, hsp], hsp_align, by simp only [arm64_norm, hx29],
     by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
     by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx25],
     by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27]⟩,
    ?_,
    by simp only [arm64_norm, hx8], by simp only [arm64_norm, hx0],
    by simp only [arm64_norm, hx1], by simp only [arm64_norm, hx2],
    by simp only [arm64_norm], by simp only [arm64_norm],
    ?_, ?_, ?_, ?_⟩
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write8_16_stack_320_xor _ _ _ _ hkb_len]
    exact hM.writeBytes_low 320#64 _ (by simp [slice16_length])
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write8_16_stack_320_xor _ _ _ _ hkb_len]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans hs0
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write8_16_stack_320_xor _ _ _ _ hkb_len]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans hs16
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write8_16_stack_320_xor _ _ _ _ hkb_len]
    exact readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _)
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write8_16_stack_320_xor _ _ _ _ hkb_len]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans hs48

set_option maxHeartbeats 1600000 in
theorem nfs3_chunk4_ext {b : BitVec 64} {ext : String → Option (State → State)}
    {s₀ s : State} {key : List (BitVec 8)}
    (hlen : key.length ≤ 64)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64)
    (hb : (b &&& 0xfff#64) = 0#64)
    (hpc : s.pc = b + bv% (ls_off% newFromSlice3Name + 1068))
    (hstat : s.status = .Running)
    (hR : NfsRegInv3 b s₀ s)
    (hM : NfsMemInv3 b s₀ s.mem)
    (hx8 : s.readReg64 .x8 = 0x36#64)
    (hx0 : s.readReg64 .x0 = nfsSp s₀ + 400#64)
    (hx1 : s.readReg64 .x1 = nfsSp s₀ + 288#64)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hx9 : s.readReg64 .x9 = (byteAt (keyBlock key) 48 ^^^ 0x36#8).zeroExtend 64)
    (hx10 : s.readReg64 .x10 = (byteAt (keyBlock key) 49).zeroExtend 64)
    (hs0 : s.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 0)
    (hs16 : s.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 16)
    (hs32 : s.mem.readBytes (nfsSp s₀ + 320#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 32)
    (hs48 : s.mem.readBytes (nfsSp s₀ + 336#64) 16 = slice16 (keyBlock key) 48) :
    RunsTo (tripleRatchetProgAtExt b ext) s (fun s' =>
      s'.pc = b + bv% (ls_off% newFromSlice3Name + 1260) ∧
      s'.status = .Running ∧
      NfsRegInv3 b s₀ s' ∧
      NfsMemInv3 b s₀ s'.mem ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧
      s'.readReg64 .x2 = 1#64 ∧
      s'.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8) ∧
      s'.mem.readBytes (nfsSp s₀) 32 =
        (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) := by
  generalize hPost : (fun s' : State => _) = Post
  obtain ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩ := hR
  have hRW_stack : s.mem.RW (nfsSp s₀) 544 := hM.rw_stack
  have hread_iv : s.mem.Readable (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 := hM.readable_iv
  have hdisj_iv : DisjointRegions (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 (nfsSp s₀) 544 := hM.disj_iv_stack
  have hread_iv_eq := read64_write8_stack_iv hM.disj_iv_stack
  have hal_464 : ((nfsSp s₀ + 464#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_464_align hal
  have hkb_len : (keyBlock key).length = 64 := keyBlock_length hlen
  obtain ⟨-, -, hb50, hb51, hb52, hb53, hb54, hb55,
          hb56, hb57, hb58, hb59, hb60, hb61, hb62, hb63⟩ :=
    read8_16_of_readBytes_slice16 s.mem (nfsSp s₀) 336#64 (keyBlock key) 48 hs48
  simp only [Nat.add_zero, Nat.reduceAdd, BitVec.reduceAdd] at hb50 hb51 hb52 hb53 hb54 hb55 hb56 hb57 hb58 hb59 hb60 hb61 hb62 hb63
  iterate 48 nfs3x_step
  subst hPost
  refine RunsTo.refl ?_
  set ivsw := (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16
  set iv := shaStateBytes sha256IV
  have hivsw_len : ivsw.length = 32 := by simp [ivsw, shaStateBytes_length]
  have hiv_len : iv.length = 32 := shaStateBytes_length sha256IV
  set m_xor := s.mem.writeBytes (nfsSp s₀ + 336#64) (slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 48)
  set m_final := (m_xor.writeBytes (nfsSp s₀) ivsw).writeBytes (nfsSp s₀ + 400#64) iv
  have hM_final : NfsMemInv3 b s₀ m_final :=
    ((hM.writeBytes_low 336#64 _ (by simp [slice16_length])).writeBytes_zero
      ivsw (by simp [hivsw_len])).writeBytes_low
      400#64 iv (by simp [hiv_len])
  have hist_final : m_final.readBytes (nfsSp s₀ + 400#64) 32 = iv :=
    Layout.readBytes_writeBytes_eq _ (nfsSp s₀ + 400#64) iv 32 hiv_len (by decide)
  have hivsw_final : m_final.readBytes (nfsSp s₀) 32 = ivsw := by
    rw [Layout.readBytes_writeBytes_of_disjoint _ (nfsSp s₀ + 400#64) iv (nfsSp s₀) 32
          (by rw [hiv_len]; clear * -; simp only [DisjointRegions]; bv_omega) (by decide),
        Layout.readBytes_writeBytes_eq m_xor (nfsSp s₀) ivsw 32 hivsw_len (by decide)]
  have hblk_final : m_final.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8) := by
    refine NewFromSlice3Proof.readBytes_64_of_four_slice16 m_final (nfsSp s₀) ((keyBlock key).map (· ^^^ 0x36#8))
      (by simp [hkb_len]) ?_ ?_ ?_ ?_
    · rw [NewFromSlice3Proof.readBytes_16_writeBytes_0_400 m_xor (nfsSp s₀) 288#64 ivsw iv hivsw_len hiv_len]
      exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans hs0
    · rw [NewFromSlice3Proof.readBytes_16_writeBytes_0_400 m_xor (nfsSp s₀) 304#64 ivsw iv hivsw_len hiv_len]
      exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans hs16
    · rw [NewFromSlice3Proof.readBytes_16_writeBytes_0_400 m_xor (nfsSp s₀) 320#64 ivsw iv hivsw_len hiv_len]
      exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans hs32
    · rw [NewFromSlice3Proof.readBytes_16_writeBytes_0_400 m_xor (nfsSp s₀) 336#64 ivsw iv hivsw_len hiv_len]
      exact readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _)
  refine ⟨by simp only [arm64_norm, hpc], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm, hsp], hsp_align, by simp only [arm64_norm, hx29],
     by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
     by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx25],
     by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27]⟩,
    ?_,
    by simp only [arm64_norm, hx0],
    by simp only [arm64_norm, hx1],
    by simp only [arm64_norm, hx2],
    ?_, ?_, ?_⟩
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_400_iv b _ s.mem (nfsSp s₀) hM.iv_bytes,
        write64_quad_0_ivsw b _ s.mem (nfsSp s₀) hM.iv_bytes,
        NewFromSlice3Proof.writeBytes_ivsw_write8_351_comm,
        write8_16_stack_336_xor _ _ _ _ hkb_len]
    exact hM_final
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_400_iv b _ s.mem (nfsSp s₀) hM.iv_bytes,
        write64_quad_0_ivsw b _ s.mem (nfsSp s₀) hM.iv_bytes,
        NewFromSlice3Proof.writeBytes_ivsw_write8_351_comm,
        write8_16_stack_336_xor _ _ _ _ hkb_len]
    exact hist_final
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_400_iv b _ s.mem (nfsSp s₀) hM.iv_bytes,
        write64_quad_0_ivsw b _ s.mem (nfsSp s₀) hM.iv_bytes,
        NewFromSlice3Proof.writeBytes_ivsw_write8_351_comm,
        write8_16_stack_336_xor _ _ _ _ hkb_len]
    exact hblk_final
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_400_iv b _ s.mem (nfsSp s₀) hM.iv_bytes,
        write64_quad_0_ivsw b _ s.mem (nfsSp s₀) hM.iv_bytes,
        NewFromSlice3Proof.writeBytes_ivsw_write8_351_comm,
        write8_16_stack_336_xor _ _ _ _ hkb_len]
    exact hivsw_final

/-- Chunks 1..4 of `new_from_slice [local#3]` (`hex:6717c → hex:6748c`), shared by both `≤ 64` and `> 64` paths. -/
theorem nfs3_chunks_1_to_4_ext {b : BitVec 64} {ext : String → Option (State → State)}
    {s₀ s : State} {m_k0 : Memory} {key : List (BitVec 8)}
    (hlen : key.length ≤ 64)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64)
    (hb : (b &&& 0xfff#64) = 0#64)
    (hpc : s.pc = b + bv% (ls_off% newFromSlice3Name + 476))
    (hstat : s.status = .Running)
    (hR : NfsRegInv3 b s₀ s)
    (hM : NfsMemInv3 b s₀ s.mem)
    (hx8 : s.readReg64 .x8 = 0x36#64)
    (hx0 : s.readReg64 .x0 = nfsSp s₀ + 400#64)
    (hx1 : s.readReg64 .x1 = nfsSp s₀ + 288#64)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hq2 : s.readVReg128 2#5 = m_k0.read64 (nfsSp s₀ + 152#64) ++ m_k0.read64 (nfsSp s₀ + 144#64))
    (hq0 : s.readVReg128 0#5 = m_k0.read64 (nfsSp s₀ + 168#64) ++ m_k0.read64 (nfsSp s₀ + 160#64))
    (hk0_drop32 : m_k0.readBytes (nfsSp s₀ + 144#64) 32 = (keyBlock key).drop 32)
    (hs0 : s.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 (keyBlock key) 0)
    (hs16 : s.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 (keyBlock key) 16) :
    RunsTo (tripleRatchetProgAtExt b ext) s (fun s' =>
      s'.pc = b + bv% (ls_off% newFromSlice3Name + 1260) ∧
      s'.status = .Running ∧
      NfsRegInv3 b s₀ s' ∧
      NfsMemInv3 b s₀ s'.mem ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧
      s'.readReg64 .x2 = 1#64 ∧
      s'.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8) ∧
      s'.mem.readBytes (nfsSp s₀) 32 =
        (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) := by
  refine (nfs3_chunk1_ext hlen hpc hstat hR hM hx8 hx0 hx1 hx2 hs0 hs16).trans fun s2 h2 => ?_
  rcases h2 with ⟨hpc2, hstat2, hR2, hM2, hx8_2, hx0_2, hx1_2, hx2_2, hx10_2, hx11_2, hq2_2, hq0_2, hs0_2, hs16_2⟩
  refine (nfs3_chunk2_ext hlen hal hpc2 hstat2 hR2 hM2 hx8_2 hx0_2 hx1_2 hx2_2 hx10_2 hx11_2
    (hq2_2.trans hq2) (hq0_2.trans hq0) hk0_drop32 hs0_2 hs16_2).trans fun s3 h3 => ?_
  rcases h3 with ⟨hpc3, hstat3, hR3, hM3, hx8_3, hx0_3, hx1_3, hx2_3, hx11_3, hx9_3, hs0_3, hs16_3, hs32_3, hs48_3⟩
  refine (nfs3_chunk3_ext hlen hpc3 hstat3 hR3 hM3 hx8_3 hx0_3 hx1_3 hx2_3 hx11_3 hx9_3
    hs0_3 hs16_3 hs32_3 hs48_3).trans fun s4 h4 => ?_
  rcases h4 with ⟨hpc4, hstat4, hR4, hM4, hx8_4, hx0_4, hx1_4, hx2_4, hx9_4, hx10_4, hs0_4, hs16_4, hs32_4, hs48_4⟩
  exact nfs3_chunk4_ext hlen hal hb hpc4 hstat4 hR4 hM4 hx8_4 hx0_4 hx1_4 hx2_4 hx9_4 hx10_4
    hs0_4 hs16_4 hs32_4 hs48_4

theorem nfs3_after_memcpy_to_compress1_ext {b : BitVec 64} {ext : String → Option (State → State)}
    {s₀ s : State} {key : List (BitVec 8)}
    (hlen : key.length ≤ 64)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64)
    (hb : (b &&& 0xfff#64) = 0#64)
    (hpc : s.pc = b + bv% (ls_off% newFromSlice3Name + 68))
    (hstat : s.status = .Running)
    (hsp : s.sp = nfsSp s₀)
    (hsp_align : (nfsSp s₀ &&& 0b1111#64) = 0#64)
    (hx29 : s.readReg64 .x29 = nfsSp s₀ + 464#64)
    (hx19 : s.readReg64 .x19 = s₀.readReg64 .x0)
    (hx22 : s.readReg64 .x22 = b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44)))
    (hx25 : s.readReg64 .x25 = s₀.readReg64 .x25)
    (hx26 : s.readReg64 .x26 = s₀.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s₀.readReg64 .x27)
    (hM_432 : NfsMemInv3 b (s₀.setMem s.mem) (s.mem.write64 (nfsSp s₀ + 432#64) 1#64))
    (hk0_64 : s.mem.readBytes (nfsSp s₀ + 112#64) 64 = keyBlock key) :
    RunsTo (tripleRatchetProgAtExt b ext) s (fun s' =>
      s'.pc = b + bv% (ls_off% newFromSlice3Name + 1260) ∧
      s'.status = .Running ∧
      NfsRegInv3 b (s₀.setMem s.mem) s' ∧
      NfsMemInv3 b (s₀.setMem s.mem) s'.mem ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧
      s'.readReg64 .x2 = 1#64 ∧
      s'.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8) ∧
      s'.mem.readBytes (nfsSp s₀) 32 =
        (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) := by
  refine (nfs3_seg0b_ext (s₀ := s₀.setMem s.mem) hlen hal hpc hstat hsp hsp_align
    hx29 hx19 hx22 hx25 hx26 hx27 hM_432 hk0_64).trans fun s1 h1 => ?_
  rcases h1 with ⟨hpc1, hstat1, hR1, hM1, hx8_1, hx0_1, hx1_1, hx2_1, hq2_1, hq0_1, hk0_1, hs0_1, hs16_1⟩
  exact nfs3_chunks_1_to_4_ext (s₀ := s₀.setMem s.mem) hlen hal hb hpc1 hstat1 hR1 hM1
    hx8_1 hx0_1 hx1_1 hx2_1 hq2_1 hq0_1 hk0_1 hs0_1 hs16_1

end CryptoVerification.SpqrV1.Kdf.Nfs3Ext
