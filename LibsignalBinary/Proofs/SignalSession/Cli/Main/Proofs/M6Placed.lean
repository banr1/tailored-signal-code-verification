/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSitesPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable `main` Hop M6 (`M+0xf70 .. M+0xfb4` + `free_args`, Block `617`)

Verifies `main`'s output/cleanup epilogue (`M+0xf70 .. M+0xfb4` + `M+0xb6c .. M+0xb80`) on Block `617`
under `[LibsignalPlacement]`: optional `write_stdout`, `out` and `input` buffer deallocation, and
`free_args` into `ExitKPlaced`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.CodeLayout

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

namespace M6PlacedHelpers

theorem m6_seq_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [hCI : LsCodeInv CodeOk]
    {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : CodeOk s.mem)
    (h : SepWP prog mid s P
      (fun sm Pm => sm.pc = mid → sm.status = .Running → CodeOk sm.mem →
        SepWPp prog ret sm Pm Q Qp oom) oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, hcont⟩ | hoom⟩
  · obtain ⟨sf, hsteps', hout⟩ :=
      hcont hpcm hrunm (hCI.of_keepsFrozen hinv hsteps.keepsFrozen) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem stackAt_split_ge (sp : BitVec 64) {n m : Nat} (hle : n ≤ m) (hlt : m ≤ 2 ^ 64) :
    stackAt sp m = memRegion (sp - BitVec.ofNat 64 m) (m - n) ∗ stackAt sp n := by
  have h := ProofLib.stackAt_split_bottom sp n (m - n) (by omega)
  have heq : n + (m - n) = m := by omega
  simpa only [heq] using h

theorem spAligned_of_s0 {s0 s : State}
    (h0 : s0.spAligned = true) (hsp : s.sp = s0.sp - 1248#64) :
    s.spAligned = true := by
  simp only [State.spAligned, beq_iff_eq] at h0 ⊢
  rw [hsp]
  bv_bits

theorem extractLsb0_of_getLsbD0 {v : BitVec 64} {b : Bool} (h : v.getLsbD 0 = b) :
    v.extractLsb' 0 1 = if b then 1#1 else 0#1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi0 : i = 0 := by omega
  subst hi0
  cases b <;> simp <;> exact h

theorem bit0_of_getLsbD0 {v : BitVec 64} {b : Bool} (h : v.getLsbD 0 = b) :
    v[0] = b := h

theorem pointsTo8_entails_memRegion (a : BitVec 64) (b : BitVec 8) :
    (a ↦₈ b) ⊢ memRegion a 1 := by
  have heq : memRegion a 1 = ∃∗ b' : BitVec 8, a ↦₈ b' :=
    IsBlock.eq (IsBlock.memRegion a 1)
      (IsBlock.sepExists fun b' => IsBlock.pointsTo8 a b')
      fun _ => ⟨fun _ => ⟨_, rfl⟩, fun _ => trivial⟩
  rw [heq]
  exact Entails.sepExists_right b (Entails.refl _)

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

theorem pointsTo64_entails_memRegion (a : BitVec 64) (v : BitVec 64) :
    (a ↦₆₄ v) ⊢ memRegion a 8 := by
  rw [ProofLib.memRegion_eight a]
  exact Entails.sepExists_right v (Entails.refl _)

theorem sliceRefAt_entails_memRegion (a p : BitVec 64) (len : Nat) :
    sliceRefAt a p len ⊢ memRegion a 16 := by
  unfold sliceRefAt
  rw [show (16 : Nat) = 8 + 8 by rfl, memRegion_split a 8 8 (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion a p)
    (pointsTo64_entails_memRegion (a + 8#64) (BitVec.ofNat 64 len))

theorem arrayAt_sliceRef_entails_memRegion64 :
    ∀ (ps : List (BitVec 64 × List (BitVec 8))) (buf : BitVec 64),
      ps.length * 16 ≤ 2 ^ 64 →
      arrayAt (fun pb a => sliceRefAt a pb.1 pb.2.length) 16 buf ps ⊢
        memRegion buf (ps.length * 16)
  | [], buf, _ => by
    simp only [arrayAt, List.length_nil, Nat.zero_mul, memRegion_zero]
    exact Entails.refl _
  | pb :: ps, buf, hlen => by
    simp only [List.length_cons] at hlen
    have hlen' : ps.length * 16 ≤ 2 ^ 64 := by omega
    simp only [arrayAt, List.length_cons]
    rw [show (ps.length + 1) * 16 = 16 + ps.length * 16 by omega,
      memRegion_split buf 16 (ps.length * 16) (by omega)]
    exact sepConj_mono (sliceRefAt_entails_memRegion buf pb.1 pb.2.length)
      (arrayAt_sliceRef_entails_memRegion64 ps (buf + 16#64) hlen')

def ownedBytesRest (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  if cap = 0 then emp
  else A.live ptr cap.toNat 1 ∗
    memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)

theorem ownedBytes_unpack (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    ownedBytes A cap ptr (BitVec.ofNat 64 bs.length) bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        ((ptr ↦ₛ bs) ∗ ownedBytesRest A cap ptr bs) := by
  unfold ownedBytes ownedBytesRest
  refine Entails.pure_left fun ⟨_, hlen, hlt, hp⟩ => Entails.pure_right ⟨hlen, hlt, hp⟩ ?_
  by_cases h0 : cap = 0
  · subst h0
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst hbs
    simp only [↓reduceIte, pointsToBytes_nil, emp_sepConj]
    exact Entails.refl _
  · simp only [h0, ↓reduceIte]
    exact Entails.of_eq (by ac_rfl)

theorem ownedBytes_free_zero (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8))
    (hlen : bs.length ≤ (0#64 : BitVec 64).toNat) :
    ((ptr ↦ₛ bs) ∗ ownedBytesRest A 0#64 ptr bs) ⊢ emp := by
  have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
  subst hbs
  unfold ownedBytesRest
  have h0 : (0#64 : BitVec 64) = 0 := rfl
  simp only [h0, ↓reduceIte, pointsToBytes_nil, emp_sepConj]
  exact Entails.refl _

theorem ownedBytes_free_ne (A : RustAlloc) {cap ptr : BitVec 64} {bs : List (BitVec 8)}
    (hne : cap ≠ 0#64) (hlen : bs.length ≤ cap.toNat) (hlt : cap.toNat < 2 ^ 63) :
    ((ptr ↦ₛ bs) ∗ ownedBytesRest A cap ptr bs) ⊢
      A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat := by
  have hne' : cap ≠ 0 := hne
  unfold ownedBytesRest
  simp only [hne', ↓reduceIte]
  have h1 : (ptr ↦ₛ bs) ∗ (A.live ptr cap.toNat 1 ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
      A.live ptr cap.toNat 1 ∗
        ((ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
    ac_rfl
  rw [h1]
  refine sepConj_mono_right ?_
  have h2 : cap.toNat = bs.length + (cap.toNat - bs.length) := by omega
  conv => rhs; rw [h2, memRegion_split ptr bs.length (cap.toNat - bs.length) (by omega)]
  exact sepConj_mono_left (pointsToBytes_entails_memRegion bs ptr (by omega))

theorem layoutOk_u8_of_ne {cap : BitVec 64} (hne : cap ≠ 0#64) (hlt : cap.toNat < 2 ^ 63) :
    LayoutOk cap.toNat 1 := by
  have hpos : 0 < cap.toNat := by bv_omega
  exact ⟨hpos, ⟨0, rfl⟩, by omega⟩

theorem layoutOk_slice_of_ne {cap : BitVec 64} (hne : cap ≠ 0#64) (hlt : cap.toNat * 16 < 2 ^ 63) :
    LayoutOk (cap.toNat * 16) 8 := by
  have hpos : 0 < cap.toNat := by bv_omega
  exact ⟨by omega, ⟨3, rfl⟩, by omega⟩

theorem shl4_toNat_eq {cap : BitVec 64} (hlt : cap.toNat * 16 < 2 ^ 63) :
    (cap <<< 4#64).toNat = cap.toNat * 16 := by
  have h1 : cap <<< 4#64 = cap * 16#64 := by bv_bits
  rw [h1, BitVec.toNat_mul]
  change (cap.toNat * 16) % (2 ^ 64) = cap.toNat * 16
  exact Nat.mod_eq_of_lt (by omega)

theorem argsBuf_free_zero (A : RustAlloc) (buf : BitVec 64)
    (ps : List (BitVec 64 × List (BitVec 8))) :
    argsBuf A 0#64 buf ps ⊢ emp := by
  unfold argsBuf vecBuf
  have h0 : (0#64 : BitVec 64) = 0 := rfl
  simp only [h0, ↓reduceIte]
  exact Entails.pure_left fun _ => Entails.refl _

theorem argsBuf_free_ne (A : RustAlloc) {cap buf : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} (hne : cap ≠ 0#64) :
    argsBuf A cap buf ps ⊢
      ⌜cap.toNat * 16 < 2 ^ 63⌝ ∗ A.live buf (cap.toNat * 16) 8 ∗
        memRegion buf (cap.toNat * 16) := by
  have hne' : cap ≠ 0 := hne
  unfold argsBuf vecBuf
  simp only [hne', ↓reduceIte]
  refine Entails.pure_left fun ⟨hps, hlt, _⟩ => Entails.pure_right hlt ?_
  refine sepConj_mono_right ?_
  have hsplit : cap.toNat * 16 = ps.length * 16 + (cap.toNat - ps.length) * 16 := by
    have : ps.length + (cap.toNat - ps.length) = cap.toNat := by omega
    calc cap.toNat * 16 = (ps.length + (cap.toNat - ps.length)) * 16 := by rw [this]
      _ = ps.length * 16 + (cap.toNat - ps.length) * 16 := Nat.add_mul _ _ 16
  conv => rhs; rw [hsplit, memRegion_split buf (ps.length * 16) ((cap.toNat - ps.length) * 16) (by omega)]
  exact sepConj_mono_left (arrayAt_sliceRef_entails_memRegion64 ps buf (by omega))

def m6CellsPlacedRest (fsp : BitVec 64) : SepProp :=
  memRegion (fsp + BitVec.ofNat 64 0) (0 - 0) ∗
    memRegion (fsp + BitVec.ofNat 64 8) (8 - 8) ∗
    memRegion (fsp + BitVec.ofNat 64 16) (16 - 16) ∗
    memRegion (fsp + BitVec.ofNat 64 24) (24 - 24) ∗
    memRegion (fsp + BitVec.ofNat 64 32) (80 - 32) ∗
    memRegion (fsp + BitVec.ofNat 64 88) (0x480 - 88)

theorem m6CellsPlaced_eq (fsp outCap outPtr outLen inCap inPtr : BitVec 64) :
    locals fsp (m6CellsPlaced fsp outCap outPtr outLen inCap inPtr) =
      ((fsp ↦₆₄ outLen) ∗ ((fsp + 8#64) ↦₆₄ outCap) ∗
        ((fsp + 16#64) ↦₆₄ inCap) ∗ ((fsp + 24#64) ↦₆₄ outPtr) ∗
        ((fsp + 80#64) ↦₆₄ inPtr) ∗ m6CellsPlacedRest fsp) := by
  simp only [locals, localsFrom, m6CellsPlaced, cell, m6CellsPlacedRest, BitVec.add_zero]
  ac_rfl

theorem m6CellsPlacedRest_entails_memRegion (fsp outCap outPtr outLen inCap inPtr : BitVec 64) :
    ((fsp ↦₆₄ outLen) ∗ ((fsp + 8#64) ↦₆₄ outCap) ∗
      ((fsp + 16#64) ↦₆₄ inCap) ∗ ((fsp + 24#64) ↦₆₄ outPtr) ∗
      ((fsp + 80#64) ↦₆₄ inPtr) ∗ m6CellsPlacedRest fsp) ⊢ memRegion fsp 0x480 := by
  unfold m6CellsPlacedRest
  simp only [Nat.sub_self, memRegion_zero, emp_sepConj, BitVec.add_zero]
  have h1 :
      (fsp ↦₆₄ outLen) ∗ ((fsp + 8#64) ↦₆₄ outCap) ∗
        ((fsp + 16#64) ↦₆₄ inCap) ∗ ((fsp + 24#64) ↦₆₄ outPtr) ∗
        ((fsp + 80#64) ↦₆₄ inPtr) ∗
        (memRegion (fsp + 32#64) 48 ∗ memRegion (fsp + 88#64) 1064) =
      (fsp ↦₆₄ outLen) ∗ ((fsp + 8#64) ↦₆₄ outCap) ∗
        ((fsp + 16#64) ↦₆₄ inCap) ∗ ((fsp + 24#64) ↦₆₄ outPtr) ∗
        memRegion (fsp + 32#64) 48 ∗ ((fsp + 80#64) ↦₆₄ inPtr) ∗
        memRegion (fsp + 88#64) 1064 := by
    ac_rfl
  rw [h1]
  have hsplit :
      memRegion fsp 0x480 =
        memRegion fsp 8 ∗ memRegion (fsp + 8#64) 8 ∗ memRegion (fsp + 16#64) 8 ∗
          memRegion (fsp + 24#64) 8 ∗ memRegion (fsp + 32#64) 48 ∗
          memRegion (fsp + 80#64) 8 ∗ memRegion (fsp + 88#64) 1064 := by
    have s1 := memRegion_split fsp 8 1144 (by decide)
    have s2 := memRegion_split (fsp + 8#64) 8 1136 (by decide)
    have s3 := memRegion_split (fsp + 16#64) 8 1128 (by decide)
    have s4 := memRegion_split (fsp + 24#64) 8 1120 (by decide)
    have s5 := memRegion_split (fsp + 32#64) 48 1072 (by decide)
    have s6 := memRegion_split (fsp + 80#64) 8 1064 (by decide)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at s1 s2 s3 s4 s5 s6
    rw [show (0x480 : Nat) = 8 + 1144 by rfl, s1,
      show (1144 : Nat) = 8 + 1136 by rfl, s2,
      show (1136 : Nat) = 8 + 1128 by rfl, s3,
      show (1128 : Nat) = 8 + 1120 by rfl, s4,
      show (1120 : Nat) = 48 + 1072 by rfl, s5,
      show (1072 : Nat) = 8 + 1064 by rfl, s6]
  rw [hsplit]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono_right (sepConj_mono_left (pointsTo64_entails_memRegion _ _))))))

theorem step_writeStdout_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [hCI : LsCodeInv CodeOk]
    {H : LibsignalHooks} {hookStack : Nat} {fsp ret_pc ret outPtr : BitVec 64} {out : List (BitVec 8)}
    {files0 : String → Option FsEntry} {tr0 : List TraceEvent}
    {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hw : subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsWriteStdoutSym)
      (withLsRoCl lsmpl (writeStdoutSpecPlaced hookStack)))
    (hpc : s.pc = lsρ lsWriteStdoutSym)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = fsp)
    (hal : s.spAligned = true)
    (hinv : CodeOk s.mem)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = outPtr)
    (hx1 : (s.readReg64 .x1).toNat = out.length)
    (hfiles_eq : s.fs.files = files0)
    (htr_eq : s.trace = tr0)
    (hP : P ⊢ (outPtr ↦ₛ out) ∗ stackAt fsp hookStack ∗ F)
    (hk : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = fsp →
      CalleeSavedPreserved s sm →
      CodeOk sm.mem →
      sm.readReg64 .x0 = 0#64 →
      sm.fs.files = files0 →
      tr0 <+: sm.trace →
      ProcessOutcome.traceStreamBytes .stdout sm.trace =
        ProcessOutcome.traceStreamBytes .stdout tr0 ++ out →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret sm
        ((outPtr ↦ₛ out) ∗ stackAt fsp hookStack ∗ F) Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret s P Q Qp oom := by
  refine main_call_rocl (x := WriteStdoutGhost.mk outPtr out) hw hinv hpc hrun hal hlr (F := F) ?_ (hnext := ?_)
  · refine Entails.trans hP ?_
    dsimp only [writeStdoutSpecPlaced]
    simp only [hsp_eq, sepConj_assoc]
    apply Entails.pure_right ⟨hx0, hx1⟩
    exact Entails.of_eq (by ac_rfl)
  · intro sm hinv_m hpcm hrunm hspm hcsm
    dsimp only [writeStdoutSpecPlaced]
    rw [hsp_eq, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0m, hfiles, hpref, hstdout⟩ => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hk sm hpcm hrunm (hspm.trans hsp_eq) hcsm hinv_m hx0m
        (hfiles.trans hfiles_eq) (htr_eq ▸ hpref) (htr_eq ▸ hstdout))

theorem step_dealloc_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [hCI : LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks}
    {fsp p ret_pc ret : BitVec 64} {size align : Nat}
    {files0 : String → Option FsEntry} {tr0 : List TraceEvent}
    {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hda : subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsRustDeallocSymCli)
      (withLsRoCl lsmpl (rustDeallocExternSpecWithStack A extHookStack).keepsFs))
    (hpc : s.pc = lsρ lsRustDeallocSymCli)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = fsp)
    (hal : s.spAligned = true)
    (hinv : CodeOk s.mem)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = p)
    (hx1 : (s.readReg64 .x1).toNat = size)
    (hx2 : (s.readReg64 .x2).toNat = align)
    (hlay : LayoutOk size align)
    (hfiles_eq : s.fs.files = files0)
    (htr_eq : s.trace = tr0)
    (hP : P ⊢ A.pool ∗ A.live p size align ∗ memRegion p size ∗ stackAt fsp extHookStack ∗ F)
    (hk : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = fsp →
      CalleeSavedPreserved s sm →
      CodeOk sm.mem →
      sm.trace = tr0 →
      sm.fs.files = files0 →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret sm
        (A.pool ∗ stackAt fsp extHookStack ∗ F) Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret s P Q Qp oom := by
  refine main_call_rocl (x := (p, size, align)) hda hinv hpc hrun hal hlr (F := F) ?_ (hnext := ?_)
  · refine Entails.trans hP ?_
    dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack]
    simp only [hsp_eq, sepConj_assoc]
    apply Entails.pure_right ⟨hx0, hx1, hx2, hlay⟩
    exact Entails.of_eq (by ac_rfl)
  · intro sm hinv_m hpcm hrunm hspm hcsm
    dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack]
    rw [hsp_eq, sepConj_assoc, sepConj_assoc]
    refine SepWPp.pure_elim fun hfs_eq => ?_
    refine SepWPp.pure_elim fun htrm => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hk sm hpcm hrunm (hspm.trans hsp_eq) hcsm hinv_m
        (htrm.trans htr_eq) ((congrArg FsState.files hfs_eq).trans hfiles_eq))

end M6PlacedHelpers

/-! ## Complete end-to-end binary proof of `main_m6_placed` (`M+0xf70 .. M+0xfb4` + `free_args`) -/

set_option maxHeartbeats 1600000 in
theorem main_m6_proof_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustAlloc}
    {uuidParse : UuidParser} {io : IoModel} {s0 s : State} {ok : Bool} {n : Nat}
    {stk hookStack resStack : Nat} {buf outCap outPtr inCap inPtr : BitVec 64}
    {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack)
    (hio : MainIoPlaced A H io hookStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs : AtM6Placed CodeOk s0 s ok n buf)
    (hexit : ExitKPlaced CodeOk H A s0 stk
      (fun code s' => s'.fs.files = s.fs.files ∧
        (if ok then code = 0 ∧ s.trace <+: s'.trace ∧
            ProcessOutcome.traceStreamBytes .stdout s'.trace =
            ProcessOutcome.traceStreamBytes .stdout s.trace ++ out
         else code = 2 ∧ s'.trace = s.trace)) Q Qp) :
    ProofLib.SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s
      (ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out ∗
        ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
        argsBuf A (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m6CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) outCap outPtr
            (BitVec.ofNat 64 out.length) inCap inPtr) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool ∗ anyHeap)
      Q Qp (mainOom s0) := by
  have hdealloc : subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsRustDeallocSymCli)
      (withLsRoCl lsmpl (rustDeallocExternSpecWithStack A extHookStack).keepsFs) :=
    main_dealloc_fs_placed_ok hc.allocFs
  have hwstdout : subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsWriteStdoutSym)
      (withLsRoCl lsmpl (writeStdoutSpecPlaced hookStack)) :=
    hio.writeStdout
  clear hc hio
  refine SepWPp.weaken_pre
    (sepConj_mono (M6PlacedHelpers.ownedBytes_unpack A outCap outPtr out)
      (sepConj_mono_left (M6PlacedHelpers.ownedBytes_unpack A inCap inPtr inp))) ?_
  rw [M6PlacedHelpers.m6CellsPlaced_eq]
  change SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s
    ((⌜out.length ≤ outCap.toNat ∧ outCap.toNat < 2 ^ 63 ∧ outPtr ≠ 0⌝ ∗
      ((outPtr ↦ₛ out) ∗ M6PlacedHelpers.ownedBytesRest A outCap outPtr out)) ∗
      ((⌜inp.length ≤ inCap.toNat ∧ inCap.toNat < 2 ^ 63 ∧ inPtr ≠ 0⌝ ∗
        ((inPtr ↦ₛ inp) ∗ M6PlacedHelpers.ownedBytesRest A inCap inPtr inp)) ∗
        argsBuf A (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        (((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
          ((s0.sp - 1248#64 + 8#64) ↦₆₄ outCap) ∗ ((s0.sp - 1248#64 + 16#64) ↦₆₄ inCap) ∗
          ((s0.sp - 1248#64 + 24#64) ↦₆₄ outPtr) ∗ ((s0.sp - 1248#64 + 80#64) ↦₆₄ inPtr) ∗
          M6PlacedHelpers.m6CellsPlacedRest (s0.sp - 1248#64)) ∗
        stackAt (s0.sp - 1248#64) (stk - mainFrameSize) ∗ A.pool ∗ anyHeap))
    Q Qp (mainOom s0)
  have hpure_pull :
      (⌜out.length ≤ outCap.toNat ∧ outCap.toNat < 2 ^ 63 ∧ outPtr ≠ 0⌝ ∗
        ((outPtr ↦ₛ out) ∗ M6PlacedHelpers.ownedBytesRest A outCap outPtr out)) ∗
        ((⌜inp.length ≤ inCap.toNat ∧ inCap.toNat < 2 ^ 63 ∧ inPtr ≠ 0⌝ ∗
          ((inPtr ↦ₛ inp) ∗ M6PlacedHelpers.ownedBytesRest A inCap inPtr inp)) ∗
          argsBuf A (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
          (((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
            ((s0.sp - 1248#64 + 8#64) ↦₆₄ outCap) ∗ ((s0.sp - 1248#64 + 16#64) ↦₆₄ inCap) ∗
            ((s0.sp - 1248#64 + 24#64) ↦₆₄ outPtr) ∗ ((s0.sp - 1248#64 + 80#64) ↦₆₄ inPtr) ∗
            M6PlacedHelpers.m6CellsPlacedRest (s0.sp - 1248#64)) ∗
          stackAt (s0.sp - 1248#64) (stk - mainFrameSize) ∗ A.pool ∗ anyHeap) =
      ⌜out.length ≤ outCap.toNat ∧ outCap.toNat < 2 ^ 63 ∧ outPtr ≠ 0⌝ ∗
        ⌜inp.length ≤ inCap.toNat ∧ inCap.toNat < 2 ^ 63 ∧ inPtr ≠ 0⌝ ∗
        (((outPtr ↦ₛ out) ∗ M6PlacedHelpers.ownedBytesRest A outCap outPtr out) ∗
          ((inPtr ↦ₛ inp) ∗ M6PlacedHelpers.ownedBytesRest A inCap inPtr inp) ∗
          argsBuf A (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
          ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
          ((s0.sp - 1248#64 + 8#64) ↦₆₄ outCap) ∗ ((s0.sp - 1248#64 + 16#64) ↦₆₄ inCap) ∗
          ((s0.sp - 1248#64 + 24#64) ↦₆₄ outPtr) ∗ ((s0.sp - 1248#64 + 80#64) ↦₆₄ inPtr) ∗
          M6PlacedHelpers.m6CellsPlacedRest (s0.sp - 1248#64) ∗
          stackAt (s0.sp - 1248#64) (stk - mainFrameSize) ∗
          A.pool ∗ anyHeap) := by
    ac_rfl
  rw [hpure_pull]
  refine SepWPp.pure_elim fun ⟨hout_le, hout_lt, _⟩ => ?_
  refine SepWPp.pure_elim fun ⟨hin_le, hin_lt, _⟩ => ?_
  rcases hs with ⟨⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩, hw22, hx19, hx24⟩
  change s.pc = (blkPl_617).base + 3952#64 at hpc
  change s.sp = s0.sp - 1248#64 at hsp
  change s.readReg64 (.gpr 29#5) = s0.sp - 96#64 at hfp
  change s.vregs.calleeSaved = s0.vregs.calleeSaved at hvregs
  have hsub_le64 : stk - mainFrameSize ≤ 2 ^ 64 := by omega
  have hhook_le : hookStack ≤ stk - mainFrameSize := by omega
  have hext_le : extHookStack ≤ stk - mainFrameSize := by omega
  suffices hfrom_f8c : ∀ (s1 : State) (code : Nat),
      s1.pc = (blkPl_617).base + 3980#64 →
      s1.status = .Running →
      s1.sp = s0.sp - 1248#64 →
      s1.readReg64 (.gpr 29#5) = s0.sp - 96#64 →
      CodeOk s1.mem →
      s1.vregs.calleeSaved = s0.vregs.calleeSaved →
      s1.readReg64 (.gpr 19#5) = buf →
      (s1.readReg64 (.gpr 26#5)).setWidth 32 = BitVec.ofNat 32 code →
      s1.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n →
      s1.fs.files = s.fs.files →
      (if ok then code = 0 ∧ s.trace <+: s1.trace ∧
          ProcessOutcome.traceStreamBytes .stdout s1.trace =
            ProcessOutcome.traceStreamBytes .stdout s.trace ++ out
       else code = 2 ∧ s1.trace = s.trace) →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s1
        (((outPtr ↦ₛ out) ∗ M6PlacedHelpers.ownedBytesRest A outCap outPtr out) ∗
          ((inPtr ↦ₛ inp) ∗ M6PlacedHelpers.ownedBytesRest A inCap inPtr inp) ∗
          argsBuf A (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
          ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
          ((s0.sp - 1248#64 + 8#64) ↦₆₄ outCap) ∗ ((s0.sp - 1248#64 + 16#64) ↦₆₄ inCap) ∗
          ((s0.sp - 1248#64 + 24#64) ↦₆₄ outPtr) ∗ ((s0.sp - 1248#64 + 80#64) ↦₆₄ inPtr) ∗
          M6PlacedHelpers.m6CellsPlacedRest (s0.sp - 1248#64) ∗
          stackAt (s0.sp - 1248#64) (stk - mainFrameSize) ∗
          A.pool ∗ anyHeap)
        Q Qp (mainOom s0) by
    cases ok
    · have hbit := M6PlacedHelpers.extractLsb0_of_getLsbD0 hw22
      have hb0 := M6PlacedHelpers.bit0_of_getLsbD0 hw22
      rw [← hsp]
      apply M6PlacedHelpers.m6_seq_placed hinv (mid := (blkPl_617).base + 3980#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
      intro _ _ hinv_m
      rw [hsp]
      refine hfrom_f8c _ 2
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        hinv_m
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm])
        ⟨rfl, by simp only [arm64_norm]⟩
    · have hbit := M6PlacedHelpers.extractLsb0_of_getLsbD0 hw22
      have hb0 := M6PlacedHelpers.bit0_of_getLsbD0 hw22
      rw [← hsp]
      apply M6PlacedHelpers.m6_seq_placed hinv (mid := lsρ lsWriteStdoutSym)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
      intro _ _ hinv_w
      rw [hsp, M6PlacedHelpers.stackAt_split_ge (s0.sp - 1248#64) hhook_le hsub_le64]
      refine M6PlacedHelpers.step_writeStdout_placed hwstdout
        (fsp := s0.sp - 1248#64) (ret_pc := (blkPl_617).base + 3972#64) (outPtr := outPtr) (out := out)
        (files0 := s.fs.files) (tr0 := s.trace)
        (F := M6PlacedHelpers.ownedBytesRest A outCap outPtr out ∗
          ((inPtr ↦ₛ inp) ∗ M6PlacedHelpers.ownedBytesRest A inCap inPtr inp) ∗
          argsBuf A (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
          ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
          ((s0.sp - 1248#64 + 8#64) ↦₆₄ outCap) ∗ ((s0.sp - 1248#64 + 16#64) ↦₆₄ inCap) ∗
          ((s0.sp - 1248#64 + 24#64) ↦₆₄ outPtr) ∗ ((s0.sp - 1248#64 + 80#64) ↦₆₄ inPtr) ∗
          M6PlacedHelpers.m6CellsPlacedRest (s0.sp - 1248#64) ∗
          memRegion ((s0.sp - 1248#64) - BitVec.ofNat 64 (stk - mainFrameSize))
            (stk - mainFrameSize - hookStack) ∗
          A.pool ∗ anyHeap)
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (M6PlacedHelpers.spAligned_of_s0 hsp0 (by simp only [arm64_norm, hsp]))
        hinv_w
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
        (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        (Entails.of_eq (by ac_rfl))
        fun sm hpcm hrunm hspm hcsm hinvm hx0m hfilesm hprefm hstdoutm => ?_
      rcases hcsm with ⟨hx19m, _, _, _, _, hx24m, _, hx26m, _, _, hfpm, hvregsm⟩
      simp only [arm64_norm, *] at hx19m hx24m hx26m hfpm hvregsm
      apply M6PlacedHelpers.m6_seq_placed hinvm (mid := (blkPl_617).base + 3980#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
      intro _ _ hinvm2
      refine SepWPp.weaken_pre ?_
        (hfrom_f8c _ 0
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          hinvm2
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          ⟨rfl, by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩)
      rw [M6PlacedHelpers.stackAt_split_ge (s0.sp - 1248#64) hhook_le hsub_le64]
      exact Entails.of_eq (by ac_rfl)
  intro s1 code hpc1 hrun1 hsp1 hfp1 hinv1 hvregs1 hx19_1 hx26_1 hx24_1 hfiles1 hout_post1
  suffices hfrom_fa0 : ∀ (s2 : State),
      s2.pc = (blkPl_617).base + 4000#64 →
      s2.status = .Running →
      s2.sp = s0.sp - 1248#64 →
      s2.readReg64 (.gpr 29#5) = s0.sp - 96#64 →
      CodeOk s2.mem →
      s2.vregs.calleeSaved = s0.vregs.calleeSaved →
      s2.readReg64 (.gpr 19#5) = buf →
      s2.readReg64 (.gpr 20#5) = inCap →
      (s2.readReg64 (.gpr 26#5)).setWidth 32 = BitVec.ofNat 32 code →
      s2.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n →
      s2.trace = s1.trace →
      s2.fs.files = s1.fs.files →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s2
        (((inPtr ↦ₛ inp) ∗ M6PlacedHelpers.ownedBytesRest A inCap inPtr inp) ∗
          argsBuf A (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
          ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
          ((s0.sp - 1248#64 + 8#64) ↦₆₄ outCap) ∗ ((s0.sp - 1248#64 + 16#64) ↦₆₄ inCap) ∗
          ((s0.sp - 1248#64 + 24#64) ↦₆₄ outPtr) ∗ ((s0.sp - 1248#64 + 80#64) ↦₆₄ inPtr) ∗
          M6PlacedHelpers.m6CellsPlacedRest (s0.sp - 1248#64) ∗
          stackAt (s0.sp - 1248#64) (stk - mainFrameSize) ∗
          A.pool ∗ anyHeap)
        Q Qp (mainOom s0) by
    by_cases hout0 : outCap = 0#64
    · subst hout0
      rw [← hsp1]
      apply M6PlacedHelpers.m6_seq_placed hinv1 (mid := (blkPl_617).base + 4000#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
      intro _ _ hinv_m
      rw [hsp1]
      refine SepWPp.weaken_pre ?_
        (hfrom_fa0 _
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          hinv_m
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm])
          (by simp only [arm64_norm]))
      refine Entails.trans
        (sepConj_mono_left (M6PlacedHelpers.ownedBytes_free_zero A outPtr out hout_le)) ?_
      rw [emp_sepConj]
      exact Entails.of_eq (by ac_rfl)
    · have hbeq : (outCap == 0#64) = false := beq_false_of_ne hout0
      rw [← hsp1]
      apply M6PlacedHelpers.m6_seq_placed hinv1 (mid := lsρ lsRustDeallocSymCli)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
      intro _ _ hinv_d
      rw [hsp1, M6PlacedHelpers.stackAt_split_ge (s0.sp - 1248#64) hext_le hsub_le64]
      refine M6PlacedHelpers.step_dealloc_placed hdealloc
        (fsp := s0.sp - 1248#64) (p := outPtr) (size := outCap.toNat) (align := 1)
        (ret_pc := (blkPl_617).base + 4000#64) (files0 := s1.fs.files) (tr0 := s1.trace)
        (F := ((inPtr ↦ₛ inp) ∗ M6PlacedHelpers.ownedBytesRest A inCap inPtr inp) ∗
          argsBuf A (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
          ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
          ((s0.sp - 1248#64 + 8#64) ↦₆₄ outCap) ∗ ((s0.sp - 1248#64 + 16#64) ↦₆₄ inCap) ∗
          ((s0.sp - 1248#64 + 24#64) ↦₆₄ outPtr) ∗ ((s0.sp - 1248#64 + 80#64) ↦₆₄ inPtr) ∗
          M6PlacedHelpers.m6CellsPlacedRest (s0.sp - 1248#64) ∗
          memRegion ((s0.sp - 1248#64) - BitVec.ofNat 64 (stk - mainFrameSize))
            (stk - mainFrameSize - extHookStack) ∗ anyHeap)
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (M6PlacedHelpers.spAligned_of_s0 hsp0 (by simp only [arm64_norm, hsp1]))
        hinv_d
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (M6PlacedHelpers.layoutOk_u8_of_ne hout0 hout_lt)
        (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        ?_
        fun sm hpcm hrunm hspm hcsm hinvm htrm hfilesm => ?_
      · have hfree := M6PlacedHelpers.ownedBytes_free_ne A (ptr := outPtr) hout0 hout_le hout_lt
        refine Entails.trans (sepConj_mono_left hfree) ?_
        exact Entails.of_eq (by ac_rfl)
      · rcases hcsm with ⟨hx19m, hx20m, _, _, _, hx24m, _, hx26m, _, _, hfpm, hvregsm⟩
        simp only [arm64_norm, *] at hx19m hx20m hx24m hx26m hfpm hvregsm
        refine SepWPp.weaken_pre ?_
          (hfrom_fa0 sm hpcm hrunm hspm hfpm hinvm hvregsm hx19m hx20m
            (by rw [hx26m]; exact hx26_1) hx24m htrm hfilesm)
        rw [M6PlacedHelpers.stackAt_split_ge (s0.sp - 1248#64) hext_le hsub_le64]
        exact Entails.of_eq (by ac_rfl)
  intro s2 hpc2 hrun2 hsp2 hfp2 hinv2 hvregs2 hx19_2 hx20_2 hx26_2 hx24_2 htr2 hfiles2
  suffices hfrom_b6c : ∀ (s3 : State),
      s3.pc = (blkPl_617).base + 2924#64 →
      s3.status = .Running →
      s3.sp = s0.sp - 1248#64 →
      s3.readReg64 (.gpr 29#5) = s0.sp - 96#64 →
      CodeOk s3.mem →
      s3.vregs.calleeSaved = s0.vregs.calleeSaved →
      s3.readReg64 (.gpr 19#5) = buf →
      (s3.readReg64 (.gpr 26#5)).setWidth 32 = BitVec.ofNat 32 code →
      s3.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n →
      s3.trace = s1.trace →
      s3.fs.files = s1.fs.files →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s3
        (argsBuf A (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
          ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
          ((s0.sp - 1248#64 + 8#64) ↦₆₄ outCap) ∗ ((s0.sp - 1248#64 + 16#64) ↦₆₄ inCap) ∗
          ((s0.sp - 1248#64 + 24#64) ↦₆₄ outPtr) ∗ ((s0.sp - 1248#64 + 80#64) ↦₆₄ inPtr) ∗
          M6PlacedHelpers.m6CellsPlacedRest (s0.sp - 1248#64) ∗
          stackAt (s0.sp - 1248#64) (stk - mainFrameSize) ∗
          A.pool ∗ anyHeap)
        Q Qp (mainOom s0) by
    by_cases hin0 : inCap = 0#64
    · subst hin0
      rw [← hsp2]
      apply M6PlacedHelpers.m6_seq_placed hinv2 (mid := (blkPl_617).base + 2924#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
      intro _ _ hinv_m
      rw [hsp2]
      refine SepWPp.weaken_pre ?_
        (hfrom_b6c _
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          hinv_m
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]))
      refine Entails.trans
        (sepConj_mono_left (M6PlacedHelpers.ownedBytes_free_zero A inPtr inp hin_le)) ?_
      rw [emp_sepConj]
      exact Entails.of_eq (by ac_rfl)
    · have hbeq : (inCap == 0#64) = false := beq_false_of_ne hin0
      rw [← hsp2]
      apply M6PlacedHelpers.m6_seq_placed hinv2 (mid := lsρ lsRustDeallocSymCli)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
      intro _ _ hinv_d
      rw [hsp2, M6PlacedHelpers.stackAt_split_ge (s0.sp - 1248#64) hext_le hsub_le64]
      refine M6PlacedHelpers.step_dealloc_placed hdealloc
        (fsp := s0.sp - 1248#64) (p := inPtr) (size := inCap.toNat) (align := 1)
        (ret_pc := (blkPl_617).base + 4020#64) (files0 := s1.fs.files) (tr0 := s1.trace)
        (F := argsBuf A (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
          ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
          ((s0.sp - 1248#64 + 8#64) ↦₆₄ outCap) ∗ ((s0.sp - 1248#64 + 16#64) ↦₆₄ inCap) ∗
          ((s0.sp - 1248#64 + 24#64) ↦₆₄ outPtr) ∗ ((s0.sp - 1248#64 + 80#64) ↦₆₄ inPtr) ∗
          M6PlacedHelpers.m6CellsPlacedRest (s0.sp - 1248#64) ∗
          memRegion ((s0.sp - 1248#64) - BitVec.ofNat 64 (stk - mainFrameSize))
            (stk - mainFrameSize - extHookStack) ∗ anyHeap)
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (M6PlacedHelpers.spAligned_of_s0 hsp0 (by simp only [arm64_norm, hsp2]))
        hinv_d
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (M6PlacedHelpers.layoutOk_u8_of_ne hin0 hin_lt)
        (by simp only [arm64_norm, hfiles2])
        (by simp only [arm64_norm, htr2])
        ?_
        fun sm hpcm hrunm hspm hcsm hinvm htrm hfilesm => ?_
      · have hfree := M6PlacedHelpers.ownedBytes_free_ne A (ptr := inPtr) hin0 hin_le hin_lt
        refine Entails.trans (sepConj_mono_left hfree) ?_
        exact Entails.of_eq (by ac_rfl)
      · rcases hcsm with ⟨hx19m, _, _, _, _, hx24m, _, hx26m, _, _, hfpm, hvregsm⟩
        simp only [arm64_norm, *] at hx19m hx24m hx26m hfpm hvregsm
        have hw26m : (sm.readReg64 (.gpr 26#5)).setWidth 32 = BitVec.ofNat 32 code := by
          rw [hx26m]; exact hx26_2
        apply M6PlacedHelpers.m6_seq_placed hinvm (mid := (blkPl_617).base + 2924#64)
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
        intro _ _ hinvm2
        refine SepWPp.weaken_pre ?_
          (hfrom_b6c _
            (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            hinvm2
            (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, hw26m])
            (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]))
        rw [M6PlacedHelpers.stackAt_split_ge (s0.sp - 1248#64) hext_le hsub_le64]
        exact Entails.of_eq (by ac_rfl)
  intro s3 hpc3 hrun3 hsp3 hfp3 hinv3 hvregs3 hx19_3 hx26_3 hx24_3 htr3 hfiles3
  set cap := BitVec.ofNat 64 n
  by_cases hcap0 : cap = 0#64
  · apply M6PlacedHelpers.m6_seq_placed hinv3 (mid := (blkPl_617).base + 2944#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
    intro hpcm hrunm hinv_m
    refine SepWPp.weaken_pre ?_ (hexit _ code ?_ ?_)
    · rw [hcap0]
      refine Entails.trans (sepConj_mono_left (M6PlacedHelpers.argsBuf_free_zero A buf ps)) ?_
      rw [emp_sepConj]
      have hcells := M6PlacedHelpers.m6CellsPlacedRest_entails_memRegion (s0.sp - 1248#64) outCap outPtr
        (BitVec.ofNat 64 out.length) inCap inPtr
      have hreord0 :
          mainSaved s0 ∗
            ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
            ((s0.sp - 1248#64 + 8#64) ↦₆₄ outCap) ∗
            ((s0.sp - 1248#64 + 16#64) ↦₆₄ inCap) ∗
            ((s0.sp - 1248#64 + 24#64) ↦₆₄ outPtr) ∗
            ((s0.sp - 1248#64 + 80#64) ↦₆₄ inPtr) ∗
            M6PlacedHelpers.m6CellsPlacedRest (s0.sp - 1248#64) ∗
            stackAt (s0.sp - 1248#64) (stk - mainFrameSize) ∗ A.pool ∗ anyHeap =
          (((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
            ((s0.sp - 1248#64 + 8#64) ↦₆₄ outCap) ∗
            ((s0.sp - 1248#64 + 16#64) ↦₆₄ inCap) ∗
            ((s0.sp - 1248#64 + 24#64) ↦₆₄ outPtr) ∗
            ((s0.sp - 1248#64 + 80#64) ↦₆₄ inPtr) ∗
            M6PlacedHelpers.m6CellsPlacedRest (s0.sp - 1248#64)) ∗
          mainSaved s0 ∗ stackAt (s0.sp - 1248#64) (stk - mainFrameSize) ∗ A.pool ∗ anyHeap := by
        ac_rfl
      rw [hreord0]
      refine Entails.trans (sepConj_mono_left hcells) ?_
      unfold retMem mainFrameSize
      exact Entails.of_eq (by ac_rfl)
    · refine ⟨⟨hpcm,
          hrunm, by simp only [arm64_norm, *],
          by simp only [arm64_norm, *], hinv_m,
          by simp only [arm64_norm, *], hsp0⟩,
        by simp only [arm64_norm, *]⟩
    · refine ⟨by simp only [arm64_norm, hfiles3, hfiles1], ?_⟩
      simp only [arm64_norm, htr3]
      exact hout_post1
  · have hbeq : (cap == 0#64) = false := beq_false_of_ne hcap0
    refine SepWPp.weaken_pre (sepConj_mono_left (M6PlacedHelpers.argsBuf_free_ne A hcap0)) ?_
    rw [sepConj_assoc, sepConj_assoc]
    refine SepWPp.pure_elim fun hcap_lt => ?_
    apply M6PlacedHelpers.m6_seq_placed hinv3 (mid := lsρ lsRustDeallocSymCli)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
    intro _ _ hinv_d
    rw [M6PlacedHelpers.stackAt_split_ge (s0.sp - 1248#64) hext_le hsub_le64]
    refine M6PlacedHelpers.step_dealloc_placed hdealloc
      (fsp := s0.sp - 1248#64) (p := buf) (size := cap.toNat * 16) (align := 8)
      (ret_pc := (blkPl_617).base + 2944#64) (files0 := s.fs.files) (tr0 := s1.trace)
      (F := mainSaved s0 ∗
        ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
        ((s0.sp - 1248#64 + 8#64) ↦₆₄ outCap) ∗ ((s0.sp - 1248#64 + 16#64) ↦₆₄ inCap) ∗
        ((s0.sp - 1248#64 + 24#64) ↦₆₄ outPtr) ∗ ((s0.sp - 1248#64 + 80#64) ↦₆₄ inPtr) ∗
        M6PlacedHelpers.m6CellsPlacedRest (s0.sp - 1248#64) ∗
        memRegion ((s0.sp - 1248#64) - BitVec.ofNat 64 (stk - mainFrameSize))
          (stk - mainFrameSize - extHookStack) ∗ anyHeap)
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (M6PlacedHelpers.spAligned_of_s0 hsp0 (by simp only [arm64_norm, hsp3]))
      hinv_d
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]; exact M6PlacedHelpers.shl4_toNat_eq hcap_lt)
      (by simp only [arm64_norm, *])
      (M6PlacedHelpers.layoutOk_slice_of_ne hcap0 hcap_lt)
      (by simp only [arm64_norm, hfiles3, hfiles1])
      (by simp only [arm64_norm, htr3])
      (Entails.of_eq (by ac_rfl))
      fun sm hpcm hrunm hspm hcsm hinvm htrm hfilesm => ?_
    rcases hcsm with ⟨_, _, _, _, _, _, _, hx26m, _, _, hfpm, hvregsm⟩
    simp only [arm64_norm, *] at hx26m hfpm hvregsm
    have hatRet : AtRetPlaced CodeOk s0 sm code :=
      ⟨⟨hpcm,
        hrunm, hspm, hfpm, hinvm, hvregsm, hsp0⟩,
       by rw [hx26m]; exact hx26_3⟩
    refine SepWPp.weaken_pre ?_
      (hexit sm code hatRet ⟨hfilesm, by rw [htrm]; exact hout_post1⟩)
    have hcells := M6PlacedHelpers.m6CellsPlacedRest_entails_memRegion (s0.sp - 1248#64) outCap outPtr
      (BitVec.ofNat 64 out.length) inCap inPtr
    have hreord :
        A.pool ∗ stackAt (s0.sp - 1248#64) extHookStack ∗
          (mainSaved s0 ∗
            ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
            ((s0.sp - 1248#64 + 8#64) ↦₆₄ outCap) ∗ ((s0.sp - 1248#64 + 16#64) ↦₆₄ inCap) ∗
            ((s0.sp - 1248#64 + 24#64) ↦₆₄ outPtr) ∗ ((s0.sp - 1248#64 + 80#64) ↦₆₄ inPtr) ∗
            M6PlacedHelpers.m6CellsPlacedRest (s0.sp - 1248#64) ∗
            memRegion ((s0.sp - 1248#64) - BitVec.ofNat 64 (stk - mainFrameSize))
              (stk - mainFrameSize - extHookStack) ∗ anyHeap) =
        ((((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
          ((s0.sp - 1248#64 + 8#64) ↦₆₄ outCap) ∗ ((s0.sp - 1248#64 + 16#64) ↦₆₄ inCap) ∗
          ((s0.sp - 1248#64 + 24#64) ↦₆₄ outPtr) ∗ ((s0.sp - 1248#64 + 80#64) ↦₆₄ inPtr) ∗
          M6PlacedHelpers.m6CellsPlacedRest (s0.sp - 1248#64)) ∗
          mainSaved s0 ∗
          (memRegion ((s0.sp - 1248#64) - BitVec.ofNat 64 (stk - mainFrameSize))
            (stk - mainFrameSize - extHookStack) ∗ stackAt (s0.sp - 1248#64) extHookStack) ∗
          A.pool ∗ anyHeap) := by
      ac_rfl
    rw [hreord, ← M6PlacedHelpers.stackAt_split_ge (s0.sp - 1248#64) hext_le hsub_le64]
    refine Entails.trans (sepConj_mono_left hcells) ?_
    unfold retMem mainFrameSize
    exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SignalSession.Cli.MainHops
