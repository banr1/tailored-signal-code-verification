/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.Repr
public import LibsignalBinary.Proofs.SpqrV1.Drop.Decodes
public import LibsignalBinary.Proofs.SpqrV1.Drop.DropCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderRepr
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Drop Glue for `proto::pq_ratchet::PolynomialEncoder` and `Option<PolynomialEncoder>`

Proves subroutine contracts for:
- `core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>` (`0x4c500`, Block `271`, 52 instructions)
- `core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::PolynomialEncoder>> [local#1]` (`0x35218`, Block `132`, 57 instructions)
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Layout.L14
open Lean Meta Elab Tactic ProofLib in
elab "ls_code_fetches " prog:ident binPfx:ident base:term:max hooks:term:max sym:str : tactic => do
  let progName ← realizeGlobalConstNoOverloadWithInfo prog
  let fnEntry ← CodeLookup.lookup progName .fnOff sym.getString
  let allOffs := ((← CodeLookup.entries progName .fnOff) ++ (← CodeLookup.entries progName .stubOff)).map (·.val)
  let a := fnEntry.val
  let some nextOff := (allOffs.filter (· > a)).foldl (fun acc x => some (acc.elim x (min · x))) none
    | throwErrorAt sym "ls_code_fetches: no symbol after {sym}"
  evalTactic (← `(tactic| code_fetches $prog $binPfx $base $hooks $(mkCIdentFrom sym fnEntry.decl) $(Syntax.mkNumLit (toString a)) $(Syntax.mkNumLit (toString (nextOff - a)))))
end CryptoVerification.SpqrV1.Layout.L14

namespace CryptoVerification.SpqrV1.Drop

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Layout.L14

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option hygiene false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local simp]
private theorem optProtoPolynomialEncoderAt_none (A : RustAlloc) (a : BitVec 64) :
    optProtoPolynomialEncoderAt A a none =
      ((a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) optProtoPolynomialEncoderNoneTailSize) := rfl

@[local simp]
private theorem optProtoPolynomialEncoderAt_some (A : RustAlloc) (a : BitVec 64)
    (pb : ProtoPolynomialEncoder) :
    optProtoPolynomialEncoderAt A a (some pb) = protoPolynomialEncoderAt A a pb := rfl

/-! ## Stack Frame Helpers (`48` B and `64` B Frames) and Stride-24 Arithmetic -/

/-- Stack budget for a 64-byte (`0x40`) frame calling `__rust_dealloc`. -/
abbrev dropStack64 : Nat := allocHookStack + 64

theorem stackAt_dropStack64_split (sp : BitVec 64) :
    stackAt sp dropStack64 =
      stackAt (sp - 64#64) allocHookStack ∗ cells (sp - 64#64) 8 :=
  stackAt_split_cells sp allocHookStack 8 (by decide)

theorem stackAt_dropStack64_split_bottom (sp : BitVec 64) :
    stackAt sp dropStack64 = memRegion (sp - 4160#64) 64 ∗ stackAt sp allocHookStack :=
  stackAt_split_bottom sp allocHookStack 64 (by decide)

theorem cells8_sub64_entails (sp fp lr x23 w3 x22 x21 x20 x19 : BitVec 64) :
    ((sp - 64#64) ↦₆₄ fp) ∗ ((sp - 56#64) ↦₆₄ lr) ∗
      ((sp - 48#64) ↦₆₄ x23) ∗ ((sp - 40#64) ↦₆₄ w3) ∗
      ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    cells (sp - 64#64) 8 := by
  cells_unfold
  exact Entails.sepExists_right fp (Entails.sepExists_right lr
    (Entails.sepExists_right x23 (Entails.sepExists_right w3
      (Entails.sepExists_right x22 (Entails.sepExists_right x21
        (Entails.sepExists_right x20 (Entails.sepExists_right x19 (Entails.refl _))))))))

theorem stack_restore_64_allocHook (sp fp lr x23 w3 x22 x21 x20 x19 : BitVec 64) :
    stackAt (sp - 64#64) allocHookStack ∗
      (((sp - 64#64) ↦₆₄ fp) ∗ ((sp - 56#64) ↦₆₄ lr) ∗
       ((sp - 48#64) ↦₆₄ x23) ∗ ((sp - 40#64) ↦₆₄ w3) ∗
       ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
       ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ⊢
    stackAt sp dropStack64 := by
  rw [stackAt_dropStack64_split sp]
  exact sepConj_mono_right (cells8_sub64_entails sp fp lr x23 w3 x22 x21 x20 x19)

/-- Callee-saved registers not saved in `[sp..sp+64]` when `x19..x23, x29, x30` ARE saved in `[sp..sp+64]`. -/
@[reducible]
def Saved64Preserved (s0 s : State) (fsp : BitVec 64) : Prop :=
  s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  s.sp = fsp ∧
  s.trace = s0.trace ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

theorem ofNat_ne_zero_of_pos_24 {n : Nat} (hpos : 0 < n) (hlt : n * 24 < 2 ^ 63) :
    BitVec.ofNat 64 n ≠ 0#64 := by
  intro heq
  have h := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat] at h
  have hlt2 : n < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hlt2] at h
  omega

theorem ofNat_beq_zero_false_24 {n : Nat} (hpos : 0 < n) (hlt : n * 24 < 2 ^ 63) :
    ¬((BitVec.ofNat 64 n == 0#64) = true) := by
  rw [beq_iff_eq]
  exact ofNat_ne_zero_of_pos_24 hpos hlt

theorem ofNat_add_one_beq_one_false_24 {n : Nat} (hpos : 0 < n) (hlt : n * 24 < 2 ^ 63) :
    ¬((BitVec.ofNat 64 n + 1#64 == 1#64) = true) := by
  rw [beq_iff_eq]
  intro heq
  have h0 : BitVec.ofNat 64 n = 0#64 := by bv_omega
  exact ofNat_ne_zero_of_pos_24 hpos hlt h0

theorem add_24_add_8 (cur : BitVec 64) : cur + 24#64 + 8#64 = cur + 32#64 := by
  bv_omega

theorem cap_mul_24 {cap : BitVec 64} (h : cap.toNat * 24 < 2 ^ 63) :
    ((cap + (cap <<< 1#64)) <<< 3#64).toNat = cap.toNat * 24 := by
  have h1 : (cap <<< 1#64).toNat = cap.toNat * 2 := by
    have ha : (cap <<< 1#64).toNat = (cap.toNat <<< 1) % 2 ^ 64 := by
      simp [BitVec.toNat_shiftLeft]
    have hb : cap.toNat <<< 1 = cap.toNat * 2 := Nat.shiftLeft_eq cap.toNat 1
    rw [ha, hb, Nat.mod_eq_of_lt (by omega)]
  have h3 : (cap + (cap <<< 1#64)).toNat = cap.toNat * 3 := by
    rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt (by omega)]
    omega
  have h24 : ((cap + (cap <<< 1#64)) <<< 3#64).toNat = (cap + (cap <<< 1#64)).toNat * 8 := by
    have ha : ((cap + (cap <<< 1#64)) <<< 3#64).toNat = ((cap + (cap <<< 1#64)).toNat <<< 3) % 2 ^ 64 :=
      BitVec.toNat_shiftLeft
    have hb : (cap + (cap <<< 1#64)).toNat <<< 3 = (cap + (cap <<< 1#64)).toNat * 8 :=
      Nat.shiftLeft_eq (cap + (cap <<< 1#64)).toNat 3
    rw [ha, hb, h3, Nat.mod_eq_of_lt (by omega)]
  rw [h24, h3]
  omega

/-! ## Representation Deallocation Entailments for `ProtoPolynomialEncoder` (`56` B) -/

theorem protoPolyEncoderTail_entails_memRegion_8 (a : BitVec 64) (idx : BitVec 32) :
    ((a + 48#64) ↦₃₂ idx) ∗ memRegion (a + 52#64) 4 ⊢ memRegion (a + 48#64) 8 := by
  rw [ProofLib.memRegion_split' (b := a + 48#64) (n := 4) (k := 4)
        (b' := a + 52#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (pointsTo32_entails_memRegion _ _)

theorem protoPolyEncoderAt_entails_dealloc (A : RustAlloc) (a : BitVec 64)
    (pb : ProtoPolynomialEncoder) :
    protoPolynomialEncoderAt A a pb ⊢
      ∃∗ g : ProtoPolynomialEncoderGhost,
        ⌜pb.pts.length ≤ g.pts.cap.toNat ∧ g.pts.cap.toNat * 24 < 2 ^ 63 ∧ g.pts.ptr ≠ 0 ∧
          pb.polys.length ≤ g.polys.cap.toNat ∧ g.polys.cap.toNat * 24 < 2 ^ 63 ∧ g.polys.ptr ≠ 0⌝ ∗
        (a ↦₆₄ g.pts.cap) ∗ ((a + 8#64) ↦₆₄ g.pts.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        (if g.pts.cap = 0 then emp
         else A.live g.pts.ptr (g.pts.cap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 g.pts.ptr pb.pts ∗
           memRegion (g.pts.ptr + BitVec.ofNat 64 (pb.pts.length * 24))
             ((g.pts.cap.toNat - pb.pts.length) * 24)) ∗
        ((a + 24#64) ↦₆₄ g.polys.cap) ∗ ((a + 32#64) ↦₆₄ g.polys.ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
        (if g.polys.cap = 0 then emp
         else A.live g.polys.ptr (g.polys.cap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 g.polys.ptr pb.polys ∗
           memRegion (g.polys.ptr + BitVec.ofNat 64 (pb.polys.length * 24))
             ((g.polys.cap.toNat - pb.polys.length) * 24)) ∗
        memRegion (a + 48#64) 8 := by
  unfold protoPolynomialEncoderAt vecVecU8At vecOf vecHeaderBytes
    protoPolynomialEncoderPolysOff protoPolynomialEncoderIdxOff
    protoPolynomialEncoderPadOff protoPolynomialEncoderPadSize
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro ptsCap
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro ptsPtr
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro polysCap
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro polysPtr
  refine Entails.sepExists_right ⟨⟨ptsCap, ptsPtr⟩, ⟨polysCap, polysPtr⟩⟩ ?_
  unfold vecAt vecBuf vecHeader
  have ha1 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have ha2 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  have htl := protoPolyEncoderTail_entails_memRegion_8 a pb.idx
  change
    (((a ↦₆₄ ptsCap) ∗ ((a + 8#64) ↦₆₄ ptsPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length)) ∗
      (⌜pb.pts.length ≤ ptsCap.toNat ∧ ptsCap.toNat * 24 < 2 ^ 63 ∧ ptsPtr ≠ 0⌝ ∗
        if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24))
            ((ptsCap.toNat - pb.pts.length) * 24))) ∗
      ((((a + 24#64) ↦₆₄ polysCap) ∗ (((a + 24#64) + 8#64) ↦₆₄ polysPtr) ∗
        (((a + 24#64) + 16#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length)) ∗
        (⌜pb.polys.length ≤ polysCap.toNat ∧ polysCap.toNat * 24 < 2 ^ 63 ∧ polysPtr ≠ 0⌝ ∗
          if polysCap = 0 then emp
          else A.live polysPtr (polysCap.toNat * 24) 8 ∗
            arrayAt (fun bs addr => vecU8 A addr bs) 24 polysPtr pb.polys ∗
            memRegion (polysPtr + BitVec.ofNat 64 (pb.polys.length * 24))
              ((polysCap.toNat - pb.polys.length) * 24))) ∗
      ((a + 48#64) ↦₃₂ pb.idx) ∗ memRegion (a + 52#64) 4 ⊢ _
  rw [ha1, ha2]
  refine Entails.trans
    (Entails.of_eq (show _ =
      ⌜pb.pts.length ≤ ptsCap.toNat ∧ ptsCap.toNat * 24 < 2 ^ 63 ∧ ptsPtr ≠ 0⌝ ∗
      ⌜pb.polys.length ≤ polysCap.toNat ∧ polysCap.toNat * 24 < 2 ^ 63 ∧ polysPtr ≠ 0⌝ ∗
      ((a ↦₆₄ ptsCap) ∗ ((a + 8#64) ↦₆₄ ptsPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        (if ptsCap = 0 then emp
         else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
           memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24))
             ((ptsCap.toNat - pb.pts.length) * 24)) ∗
        ((a + 24#64) ↦₆₄ polysCap) ∗ ((a + 32#64) ↦₆₄ polysPtr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
        (if polysCap = 0 then emp
         else A.live polysPtr (polysCap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 polysPtr pb.polys ∗
           memRegion (polysPtr + BitVec.ofNat 64 (pb.polys.length * 24))
             ((polysCap.toNat - pb.polys.length) * 24)) ∗
        (((a + 48#64) ↦₃₂ pb.idx) ∗ memRegion (a + 52#64) 4)) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨h1, h2, h3⟩
  apply Entails.pure_left; rintro ⟨h4, h5, h6⟩
  refine Entails.pure_right ⟨h1, h2, h3, h4, h5, h6⟩ ?_
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right htl)))))))

theorem protoPolyEncoderHeaders_entails_memRegion_56
    (a ptsCap ptsPtr ptsLen polysCap polysPtr polysLen : BitVec 64) :
    (a ↦₆₄ ptsCap) ∗ ((a + 8#64) ↦₆₄ ptsPtr) ∗ ((a + 16#64) ↦₆₄ ptsLen) ∗
      ((a + 24#64) ↦₆₄ polysCap) ∗ ((a + 32#64) ↦₆₄ polysPtr) ∗ ((a + 40#64) ↦₆₄ polysLen) ∗
      memRegion (a + 48#64) 8 ⊢
    memRegion a 56 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 48) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 40) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 32) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 24) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 32#64) (n := 8) (k := 16) (b' := a + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 40#64) (n := 8) (k := 8) (b' := a + 48#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono_left (pointsTo64_entails_memRegion _ _))))))

theorem optProtoPolyEncoder_none_entails_memRegion_56 (a : BitVec 64) :
    ((a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 48) ⊢ memRegion a 56 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 48) (b' := a + 8#64) rfl rfl (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion a noneCap)

/-! ## Specifications -/

/-- Ghost arguments for `drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>` (`0x4c500`). -/
structure DropProtoPolyEncoderGhost where
  /-- Pointer to the 56-byte `ProtoPolynomialEncoder` (`x0`). -/
  a : BitVec 64
  /-- Abstract `ProtoPolynomialEncoder` model value. -/
  pb : ProtoPolynomialEncoder

def dropProtoPolyEncoderSpec (A : RustAlloc) : Spec DropProtoPolyEncoderGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗
      protoPolynomialEncoderAt A x.a x.pb ∗
      A.pool ∗ stackAt s.sp dropStack48
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a protoPolynomialEncoderSize ∗
      A.pool ∗ stackAt s0.sp dropStack48

/-- Ghost arguments for `drop_glue::<Option<spqr::proto::pq_ratchet::PolynomialEncoder>>` (`0x35218`). -/
structure DropOptProtoPolyEncoderGhost where
  /-- Pointer to the 56-byte `Option<ProtoPolynomialEncoder>` (`x0`). -/
  a : BitVec 64
  /-- Abstract `Option ProtoPolynomialEncoder` model value. -/
  optPb : Option ProtoPolynomialEncoder

def dropOptProtoPolyEncoderSpec (A : RustAlloc) : Spec DropOptProtoPolyEncoderGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗
      optProtoPolynomialEncoderAt A x.a x.optPb ∗
      A.pool ∗ stackAt s.sp dropStack64
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a protoPolynomialEncoderSize ∗
      A.pool ∗ stackAt s0.sp dropStack64

/-! ## `drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>` (`0x4c500`) -/

local macro "proto_poly_encoder_body_steps " prog:term:max entry:term:max off:term:max : tactic => `(tactic| (
  intro cur cnt bs s Frame hpc hrun hpres hx19 hx20 hx21 hx22
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A cur bs)) ?_
  apply SepWP.exists_sepConj_left; intro cap
  apply SepWP.exists_sepConj_left; intro vptr
  have hstep : SepWP $prog ($entry + $off) s
      (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8 ∗
        vecCapPtrDealloc A cap vptr) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = ptr ∧
        sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
    dsimp only [vecCapPtrDealloc]
    by_cases hcap : (cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; wp_done
    · wp_steps; wp_apply; wp_steps; refine align_pre (by rw [hsp]; ac_rfl) ?_; wp_done
  exact SepWP.strengthen_entails_const
    (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)) hstep))

local macro "proto_poly_encoder_loop_steps " entry:term:max off1:term:max off2:term:max : tactic => `(tactic| (
  intro rest
  induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur s Frame _ hlen hpc hrun hpres hx19 hx20 hx21 hx22
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine seq_clean (mid := $entry + $off1)
      (P_mid := memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) tl ∗ Frame))
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = ptr ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = cur + 8#64)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs s _ hpc hrun hpres hx19 hx20 hx21 hx22) ?_
    intro s1 hpc1 hrun1 ⟨hpres1, hx19_1, hx20_1, hx21_1, hx22_1⟩
    rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx21_1 ⊢
      rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
      wp_steps; wp_done
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx21_1
      refine seq_clean (mid := $entry + $off2)
        (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ (memRegion cur 24 ∗ Frame))
        (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = ptr ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 (bs2 :: tl2).length ∧ sm.readReg64 .x22 = (cur + 24#64) + 8#64)
        ?_ ?_
      · rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
        rw [sep_push_body]; wp_steps; rw [add_24_add_8]; wp_done
      · intro s2 hpc2 hrun2 ⟨hpres2, hx19_2, hx20_2, hx21_2, hx22_2⟩
        have hrec := ih (cur + 24#64) s2 (memRegion cur 24 ∗ Frame)
          (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hpres2 hx19_2 hx20_2 hx21_2 hx22_2
        refine SepWP.strengthen_entails_const ?_ hrec
        have hsplit := cons_len_mul bs (bs2 :: tl2) 24
        have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
        exact Entails.refl _))

local macro "proto_poly_encoder_main_steps " entry:term:max : tactic => `(tactic| (
  wp_init x s0; rcases x with ⟨a, pb⟩
  dsimp only [DropProtoPolyEncoderGhost.a, DropProtoPolyEncoderGhost.pb] at *
  refine SepWP.weaken_pre (sepConj_mono_left (protoPolyEncoderAt_entails_dealloc A a pb)) ?_
  wp_pull_exists; rename_i g
  nth_rw 1 [stackAt_dropStack48_split s0.sp]; cells_unfold; wp_pull_exists; wp_focus_pure
  rintro ⟨hpts_le, hpts_cap_lt, hpts_ptr_ne, hpolys_le, hpolys_cap_lt, hpolys_ptr_ne⟩
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  refine seq_clean (mid := $entry + 72#64)
    (P_mid := (a ↦₆₄ g.pts.cap) ∗ ((a + 8#64) ↦₆₄ g.pts.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
      (if g.pts.cap = 0 then emp
       else A.live g.pts.ptr (g.pts.cap.toNat * 24) 8 ∗ memRegion g.pts.ptr (g.pts.cap.toNat * 24)) ∗
      ((a + 24#64) ↦₆₄ g.polys.cap) ∗ ((a + 32#64) ↦₆₄ g.polys.ptr) ∗
      ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
      (if g.polys.cap = 0 then emp
       else A.live g.polys.ptr (g.polys.cap.toNat * 24) 8 ∗
         arrayAt (fun bs addr => vecU8 A addr bs) 24 g.polys.ptr pb.polys ∗
         memRegion (g.polys.ptr + BitVec.ofNat 64 (pb.polys.length * 24))
           ((g.polys.cap.toNat - pb.polys.length) * 24)) ∗
      memRegion (a + 48#64) 8 ∗ A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧
      sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.pts.ptr) ?_ ?_
  · generalize hxs : pb.pts = xs at hpts_le ⊢
    cases xs with
    | nil =>
      simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, arrayAt, emp_sepConj]
      wp_steps; refine align_pre (by ac_rfl) ?_; wp_done
    | cons bs tl =>
      have hlen_pos : 0 < (bs :: tl).length := by simp
      have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
        have : (bs :: tl).length * 24 ≤ g.pts.cap.toNat * 24 := Nat.mul_le_mul_right 24 hpts_le; omega
      have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
      have hcap_ne : g.pts.cap ≠ 0 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
      simp only [hcap_ne, ↓reduceIte]
      refine seq_clean (mid := $entry + 48#64)
        (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 g.pts.ptr (bs :: tl) ∗
          A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
          ((a ↦₆₄ g.pts.cap) ∗ ((a + 8#64) ↦₆₄ g.pts.ptr) ∗
           ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (bs :: tl).length) ∗
           A.live g.pts.ptr (g.pts.cap.toNat * 24) 8 ∗
           memRegion (g.pts.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24))
             ((g.pts.cap.toNat - (bs :: tl).length) * 24) ∗
           ((a + 24#64) ↦₆₄ g.polys.cap) ∗ ((a + 32#64) ↦₆₄ g.polys.ptr) ∗
           ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
           (if g.polys.cap = 0 then emp
            else A.live g.polys.ptr (g.polys.cap.toNat * 24) 8 ∗
              arrayAt (fun bs addr => vecU8 A addr bs) 24 g.polys.ptr pb.polys ∗
              memRegion (g.polys.ptr + BitVec.ofNat 64 (pb.polys.length * 24))
                ((g.polys.cap.toNat - pb.polys.length) * 24)) ∗
           memRegion (a + 48#64) 8 ∗
           (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧
          sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.pts.ptr ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = g.pts.ptr + 8#64) ?_ ?_
      · wp_steps; refine align_pre (by ac_rfl) ?_; wp_done
      · intro s_loop hpc_loop hrun_loop ⟨hpres_loop, hx19_loop, hx20_loop, hx21_loop, hx22_loop⟩
        refine SepWP.strengthen_entails_const ?_
          (hloop1 s0 (s0.sp - 48#64) a g.pts.ptr hfsp_align (bs :: tl) g.pts.ptr s_loop _
            (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop
            hx19_loop hx20_loop hx21_loop hx22_loop)
        have hsplit : g.pts.cap.toNat * 24 =
            (bs :: tl).length * 24 + (g.pts.cap.toNat - (bs :: tl).length) * 24 := by
          rw [← Nat.add_mul]; congr 1; omega
        have hbound : (bs :: tl).length * 24 + (g.pts.cap.toNat - (bs :: tl).length) * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; omega
        conv_rhs =>
          arg 2; arg 2; arg 2; arg 1; arg 2
          rw [hsplit, ProofLib.memRegion_split g.pts.ptr ((bs :: tl).length * 24)
                ((g.pts.cap.toNat - (bs :: tl).length) * 24) hbound]
        exact Entails.of_eq (by ac_rfl)
  · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx20_1⟩
    refine seq_clean (mid := $entry + 100#64)
      (P_mid := (a ↦₆₄ g.pts.cap) ∗ ((a + 8#64) ↦₆₄ g.pts.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        ((a + 24#64) ↦₆₄ g.polys.cap) ∗ ((a + 32#64) ↦₆₄ g.polys.ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
        (if g.polys.cap = 0 then emp
         else A.live g.polys.ptr (g.polys.cap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 g.polys.ptr pb.polys ∗
           memRegion (g.polys.ptr + BitVec.ofNat 64 (pb.polys.length * 24))
             ((g.polys.cap.toNat - pb.polys.length) * 24)) ∗
        memRegion (a + 48#64) 8 ∗ A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
    · by_cases hc : g.pts.cap = 0
      · have hc_beq : (g.pts.cap == 0#64) = true := by rw [beq_iff_eq]; exact hc
        simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp]; wp_steps; wp_done
      · have hc_beq : ¬((g.pts.cap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
        have hlsl := cap_mul_24 hpts_cap_lt
        simp only [hc, ↓reduceIte]; wp_steps
        wp_call hdealloc_raw (g.pts.ptr, g.pts.cap.toNat * 24, 8)
        refine align_pre (by rw [hsp_1]; ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      refine seq_clean (mid := $entry + 152#64)
        (P_mid := (a ↦₆₄ g.pts.cap) ∗ ((a + 8#64) ↦₆₄ g.pts.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
          ((a + 24#64) ↦₆₄ g.polys.cap) ∗ ((a + 32#64) ↦₆₄ g.polys.ptr) ∗
          ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
          (if g.polys.cap = 0 then emp
           else A.live g.polys.ptr (g.polys.cap.toNat * 24) 8 ∗ memRegion g.polys.ptr (g.polys.cap.toNat * 24)) ∗
          memRegion (a + 48#64) 8 ∗ A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
          (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧
          sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.polys.ptr) ?_ ?_
      · generalize hys : pb.polys = ys at hpolys_le ⊢
        cases ys with
        | nil =>
          simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
            BitVec.add_zero, arrayAt, emp_sepConj]
          wp_steps; refine align_pre (by ac_rfl) ?_; wp_done
        | cons bs tl =>
          have hlen_pos : 0 < (bs :: tl).length := by simp
          have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
            have : (bs :: tl).length * 24 ≤ g.polys.cap.toNat * 24 := Nat.mul_le_mul_right 24 hpolys_le; omega
          have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
          have hcap_ne : g.polys.cap ≠ 0 := by intro hc0; rw [hc0] at hpolys_le; simp at hpolys_le
          simp only [hcap_ne, ↓reduceIte]
          refine seq_clean (mid := $entry + 128#64)
            (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 g.polys.ptr (bs :: tl) ∗
              A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
              ((a ↦₆₄ g.pts.cap) ∗ ((a + 8#64) ↦₆₄ g.pts.ptr) ∗
               ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
               ((a + 24#64) ↦₆₄ g.polys.cap) ∗ ((a + 32#64) ↦₆₄ g.polys.ptr) ∗
               ((a + 40#64) ↦₆₄ BitVec.ofNat 64 (bs :: tl).length) ∗
               A.live g.polys.ptr (g.polys.cap.toNat * 24) 8 ∗
               memRegion (g.polys.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24))
                 ((g.polys.cap.toNat - (bs :: tl).length) * 24) ∗
               memRegion (a + 48#64) 8 ∗
               (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
            (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧
              sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.polys.ptr ∧
              sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = g.polys.ptr + 8#64) ?_ ?_
          · wp_steps; refine align_pre (by ac_rfl) ?_; wp_done
          · intro s_loop hpc_loop hrun_loop ⟨hpres_loop, hx19_loop, hx20_loop, hx21_loop, hx22_loop⟩
            refine SepWP.strengthen_entails_const ?_
              (hloop2 s0 (s0.sp - 48#64) a g.polys.ptr hfsp_align (bs :: tl) g.polys.ptr s_loop _
                (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop
                hx19_loop hx20_loop hx21_loop hx22_loop)
            have hsplit : g.polys.cap.toNat * 24 =
                (bs :: tl).length * 24 + (g.polys.cap.toNat - (bs :: tl).length) * 24 := by
              rw [← Nat.add_mul]; congr 1; omega
            have hbound : (bs :: tl).length * 24 + (g.polys.cap.toNat - (bs :: tl).length) * 24 ≤ 2 ^ 64 := by
              rw [← hsplit]; omega
            conv_rhs =>
              arg 2; arg 2; arg 2; arg 2; arg 2; arg 2; arg 1; arg 2
              rw [hsplit, ProofLib.memRegion_split g.polys.ptr ((bs :: tl).length * 24)
                    ((g.polys.cap.toNat - (bs :: tl).length) * 24) hbound]
            exact Entails.of_eq (by ac_rfl)
      · intro s3 hpc3 hrun3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3, hx20_3⟩
        by_cases hc : g.polys.cap = 0
        · have hc_beq : (g.polys.cap == 0#64) = true := by rw [beq_iff_eq]; exact hc
          simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp]; wp_steps
          refine SepWP.focus_weaken
            (protoPolyEncoderHeaders_entails_memRegion_56 a g.pts.cap g.pts.ptr
              (BitVec.ofNat 64 pb.pts.length) 0#64 g.polys.ptr (BitVec.ofNat 64 pb.polys.length)) (by sep_focus) ?_
          refine SepWP.focus_weaken
            (stack_restore_48_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
              (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
          wp_done
        · have hc_beq : ¬((g.polys.cap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
          have hlsl := cap_mul_24 hpolys_cap_lt
          simp only [hc, ↓reduceIte]; wp_steps
          refine SepWP.focus_weaken
            (protoPolyEncoderHeaders_entails_memRegion_56 a g.pts.cap g.pts.ptr
              (BitVec.ofNat 64 pb.pts.length) g.polys.cap g.polys.ptr (BitVec.ofNat 64 pb.polys.length)) (by sep_focus) ?_
          refine SepWP.focus_weaken
            (stack_restore_48_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
              (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
          rw [stackAt_dropStack48_split_bottom s0.sp]
          wp_call hdealloc_raw (g.polys.ptr, g.polys.cap.toNat * 24, 8)
          rw [← stackAt_dropStack48_split_bottom s0.sp]; wp_done))

private theorem drop_proto_poly_encoder_body1 {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoPolyEncoderName + bv% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" "__rustc::__rust_dealloc")) (rustDeallocSpec A))
    (s0 : State) (fsp a ptr : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = (dropProgAtExt b ext).fnAddr dropProtoPolyEncoderName + 48#64 → s.status = .Running → Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = a → s.readReg64 .x20 = ptr → s.readReg64 .x21 = cnt → s.readReg64 .x22 = cur + 8#64 →
      SepWP (dropProgAtExt b ext) ((dropProgAtExt b ext).fnAddr dropProtoPolyEncoderName + 36#64) s
        (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = ptr ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
  simp only [rustDeallocSpec] at hdealloc; dsimp only [dropProgAtExt, dropProtoPolyEncoderName, BitVec.ofNat_eq_ofNat] at *
  ls_code_fetches libsignalSessionCode spqrDropChainEpochBin b (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>"
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" = entry
  examples_hide_fetches; proto_poly_encoder_body_steps (libsignalSessionCode.rebase b (Rust.withPanics ext)) entry 36#64

private theorem drop_proto_poly_encoder_loop1 {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoPolyEncoderName + bv% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" "__rustc::__rust_dealloc")) (rustDeallocSpec A))
    (s0 : State) (fsp a ptr : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (dropProgAtExt b ext).fnAddr dropProtoPolyEncoderName + 48#64 → s.status = .Running → Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = a → s.readReg64 .x20 = ptr → s.readReg64 .x21 = BitVec.ofNat 64 rest.length → s.readReg64 .x22 = cur + 8#64 →
      SepWP (dropProgAtExt b ext) ((dropProgAtExt b ext).fnAddr dropProtoPolyEncoderName + 72#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = ptr) := by
  have hbody := drop_proto_poly_encoder_body1 (b := b) (ext := ext) hdealloc s0 fsp a ptr hfsp_align
  dsimp only [dropProgAtExt, dropProtoPolyEncoderName, BitVec.ofNat_eq_ofNat] at *
  ls_code_fetches libsignalSessionCode spqrDropChainEpochBin b (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>"
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" = entry
  examples_hide_fetches; proto_poly_encoder_loop_steps entry 36#64 48#64

private theorem drop_proto_poly_encoder_body2 {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoPolyEncoderName + bv% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" "__rustc::__rust_dealloc")) (rustDeallocSpec A))
    (s0 : State) (fsp a ptr : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = (dropProgAtExt b ext).fnAddr dropProtoPolyEncoderName + 128#64 → s.status = .Running → Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = a → s.readReg64 .x20 = ptr → s.readReg64 .x21 = cnt → s.readReg64 .x22 = cur + 8#64 →
      SepWP (dropProgAtExt b ext) ((dropProgAtExt b ext).fnAddr dropProtoPolyEncoderName + 116#64) s
        (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = ptr ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
  simp only [rustDeallocSpec] at hdealloc; dsimp only [dropProgAtExt, dropProtoPolyEncoderName, BitVec.ofNat_eq_ofNat] at *
  ls_code_fetches libsignalSessionCode spqrDropChainEpochBin b (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>"
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" = entry
  examples_hide_fetches; proto_poly_encoder_body_steps (libsignalSessionCode.rebase b (Rust.withPanics ext)) entry 116#64

private theorem drop_proto_poly_encoder_loop2 {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoPolyEncoderName + bv% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" "__rustc::__rust_dealloc")) (rustDeallocSpec A))
    (s0 : State) (fsp a ptr : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (dropProgAtExt b ext).fnAddr dropProtoPolyEncoderName + 128#64 → s.status = .Running → Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = a → s.readReg64 .x20 = ptr → s.readReg64 .x21 = BitVec.ofNat 64 rest.length → s.readReg64 .x22 = cur + 8#64 →
      SepWP (dropProgAtExt b ext) ((dropProgAtExt b ext).fnAddr dropProtoPolyEncoderName + 152#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = ptr) := by
  have hbody := drop_proto_poly_encoder_body2 (b := b) (ext := ext) hdealloc s0 fsp a ptr hfsp_align
  dsimp only [dropProgAtExt, dropProtoPolyEncoderName, BitVec.ofNat_eq_ofNat] at *
  ls_code_fetches libsignalSessionCode spqrDropChainEpochBin b (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>"
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" = entry
  examples_hide_fetches; proto_poly_encoder_loop_steps entry 116#64 128#64

/-- `core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>` (`0x4c500`, 52 insns)
    satisfies `dropProtoPolyEncoderSpec A`. -/
theorem drop_glue_proto_poly_encoder_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext) :
    subroutine_ok (dropProgAtExt b ext) ((dropProgAtExt b ext).fnAddr dropProtoPolyEncoderName) (dropProtoPolyEncoderSpec A) := by
  simp only [dropProtoPolyEncoderSpec]
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoPolyEncoderName + bv% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" "__rustc::__rust_dealloc")) (rustDeallocSpec A) :=
    sub_ok_of_addr_eq (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" "__rustc::__rust_dealloc")) (b := b) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>") (ls_stub% "__rustc::__rust_dealloc") (by decide)) hdealloc
  have hloop1 := drop_proto_poly_encoder_loop1 (b := b) (ext := ext) hdealloc_raw
  have hloop2 := drop_proto_poly_encoder_loop2 (b := b) (ext := ext) hdealloc_raw
  ls_code_fetches libsignalSessionCode spqrDropChainEpochBin b (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>"
  dsimp only [dropProgAtExt, dropProtoPolyEncoderName, protoPolynomialEncoderSize, BitVec.ofNat_eq_ofNat] at hloop1 hloop2 hdealloc_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" = entry
  examples_hide_fetches; proto_poly_encoder_main_steps entry

section PlacedProtoPolyEncoder
variable [LibsignalPlacement]

private theorem drop_proto_poly_encoder_body1_placed {A : RustAlloc} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_271).rebase (blkPl_271).base H) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (fsp a ptr : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = (blkPl_271).base + 48#64 → s.status = .Running → Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = a → s.readReg64 .x20 = ptr → s.readReg64 .x21 = cnt → s.readReg64 .x22 = cur + 8#64 →
      SepWP ((blkPC_271).rebase (blkPl_271).base H) ((blkPl_271).base + 36#64) s
        (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = ptr ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
  simp only [rustDeallocSpec] at hdealloc; proto_poly_encoder_body_steps ((blkPC_271).rebase (blkPl_271).base H) (blkPl_271).base 36#64

private theorem drop_proto_poly_encoder_loop1_placed {A : RustAlloc} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_271).rebase (blkPl_271).base H) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (fsp a ptr : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (blkPl_271).base + 48#64 → s.status = .Running → Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = a → s.readReg64 .x20 = ptr → s.readReg64 .x21 = BitVec.ofNat 64 rest.length → s.readReg64 .x22 = cur + 8#64 →
      SepWP ((blkPC_271).rebase (blkPl_271).base H) ((blkPl_271).base + 72#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = ptr) := by
  have hbody := drop_proto_poly_encoder_body1_placed hdealloc s0 fsp a ptr hfsp_align
  proto_poly_encoder_loop_steps (blkPl_271).base 36#64 48#64

private theorem drop_proto_poly_encoder_body2_placed {A : RustAlloc} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_271).rebase (blkPl_271).base H) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (fsp a ptr : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = (blkPl_271).base + 128#64 → s.status = .Running → Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = a → s.readReg64 .x20 = ptr → s.readReg64 .x21 = cnt → s.readReg64 .x22 = cur + 8#64 →
      SepWP ((blkPC_271).rebase (blkPl_271).base H) ((blkPl_271).base + 116#64) s
        (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = ptr ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
  simp only [rustDeallocSpec] at hdealloc; proto_poly_encoder_body_steps ((blkPC_271).rebase (blkPl_271).base H) (blkPl_271).base 116#64

private theorem drop_proto_poly_encoder_loop2_placed {A : RustAlloc} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_271).rebase (blkPl_271).base H) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (fsp a ptr : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (blkPl_271).base + 128#64 → s.status = .Running → Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = a → s.readReg64 .x20 = ptr → s.readReg64 .x21 = BitVec.ofNat 64 rest.length → s.readReg64 .x22 = cur + 8#64 →
      SepWP ((blkPC_271).rebase (blkPl_271).base H) ((blkPl_271).base + 152#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = ptr) := by
  have hbody := drop_proto_poly_encoder_body2_placed hdealloc s0 fsp a ptr hfsp_align
  proto_poly_encoder_loop_steps (blkPl_271).base 116#64 128#64

theorem drop_glue_proto_poly_encoder_placed_ok {A : RustAlloc} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_271).rebase (blkPl_271).base H) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_271).rebase (blkPl_271).base H) (blkPl_271).base (dropProtoPolyEncoderSpec A) := by
  simp only [dropProtoPolyEncoderSpec]
  have hdealloc_raw := hdealloc
  have hloop1 := drop_proto_poly_encoder_loop1_placed hdealloc_raw
  have hloop2 := drop_proto_poly_encoder_loop2_placed hdealloc_raw
  dsimp only [protoPolynomialEncoderSize] at *; proto_poly_encoder_main_steps (blkPl_271).base

end PlacedProtoPolyEncoder

/-! ## `drop_glue::<Option<spqr::proto::pq_ratchet::PolynomialEncoder>>` (`0x35218`) -/

local macro "opt_proto_poly_encoder_body1_steps " prog:term:max entry:term:max : tactic => `(tactic| (
  intro cur cnt bs s Frame hpc hrun hpres hx19 hx20 hx21 hx22 hx23
  rcases hpres with ⟨hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A cur bs)) ?_
  apply SepWP.exists_sepConj_left; intro cap; apply SepWP.exists_sepConj_left; intro vptr
  have hstep : SepWP $prog ($entry + 52#64) s
      (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8 ∗
        vecCapPtrDealloc A cap vptr) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm => (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        Saved64Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = ptsPtr ∧
        sm.readReg64 .x21 = ptsCap ∧ sm.readReg64 .x22 = cnt ∧ sm.readReg64 .x23 = cur + 8#64) := by
    dsimp only [vecCapPtrDealloc]
    by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; wp_done
    · wp_steps; wp_apply; wp_steps; refine align_pre (by rw [hsp]; ac_rfl) ?_; wp_done
  exact SepWP.strengthen_entails_const (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)) hstep))

local macro "opt_proto_poly_encoder_loop1_steps " entry:term:max : tactic => `(tactic| (
  intro rest; induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur s Frame _ hlen hpc hrun hpres hx19 hx20 hx21 hx22 hx23
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine seq_clean (mid := $entry + 52#64)
      (P_mid := memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) tl ∗ Frame))
      (Q := fun sm => Saved64Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧
        sm.readReg64 .x20 = ptsPtr ∧ sm.readReg64 .x21 = ptsCap ∧
        sm.readReg64 .x22 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x23 = cur + 8#64)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs s _ hpc hrun hpres hx19 hx20 hx21 hx22 hx23) ?_
    intro s1 hpc1 hrun1 ⟨hpres1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1⟩
    rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx22_1 ⊢
      rcases hpres1 with ⟨hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩; wp_steps; wp_done
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx22_1
      refine seq_clean (mid := $entry + 64#64)
        (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ (memRegion cur 24 ∗ Frame))
        (Q := fun sm => Saved64Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧
          sm.readReg64 .x20 = ptsPtr ∧ sm.readReg64 .x21 = ptsCap ∧
          sm.readReg64 .x22 = BitVec.ofNat 64 (bs2 :: tl2).length ∧ sm.readReg64 .x23 = (cur + 24#64) + 8#64) ?_ ?_
      · rcases hpres1 with ⟨hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
        rw [sep_push_body]; wp_steps; rw [add_24_add_8]; wp_done
      · intro s2 hpc2 hrun2 ⟨hpres2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2⟩
        have hrec := ih (cur + 24#64) s2 (memRegion cur 24 ∗ Frame)
          (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hpres2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2
        refine SepWP.strengthen_entails_const ?_ hrec
        have hsplit := cons_len_mul bs (bs2 :: tl2) 24
        have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
        exact Entails.refl _))

local macro "opt_proto_poly_encoder_body2_steps " prog:term:max entry:term:max : tactic => `(tactic| (
  intro cur cnt bs s Frame hpc hrun hpres hx19 hx20 hx21 hx22
  rcases hpres with ⟨hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A cur bs)) ?_
  apply SepWP.exists_sepConj_left; intro cap; apply SepWP.exists_sepConj_left; intro vptr
  have hstep : SepWP $prog ($entry + 128#64) s
      (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8 ∗
        vecCapPtrDealloc A cap vptr) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm => (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        Saved64Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = polysPtr ∧
        sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
    dsimp only [vecCapPtrDealloc]
    by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; wp_done
    · wp_steps; wp_apply; wp_steps; refine align_pre (by rw [hsp]; ac_rfl) ?_; wp_done
  exact SepWP.strengthen_entails_const (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)) hstep))

local macro "opt_proto_poly_encoder_loop2_steps " entry:term:max : tactic => `(tactic| (
  intro rest; induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur s Frame _ hlen hpc hrun hpres hx19 hx20 hx21 hx22
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine seq_clean (mid := $entry + 128#64)
      (P_mid := memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) tl ∗ Frame))
      (Q := fun sm => Saved64Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = polysPtr ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = cur + 8#64)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs s _ hpc hrun hpres hx19 hx20 hx21 hx22) ?_
    intro s1 hpc1 hrun1 ⟨hpres1, hx19_1, hx20_1, hx21_1, hx22_1⟩
    rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx21_1 ⊢
      rcases hpres1 with ⟨hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩; wp_steps; wp_done
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx21_1
      refine seq_clean (mid := $entry + 140#64)
        (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ (memRegion cur 24 ∗ Frame))
        (Q := fun sm => Saved64Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = polysPtr ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 (bs2 :: tl2).length ∧ sm.readReg64 .x22 = (cur + 24#64) + 8#64) ?_ ?_
      · rcases hpres1 with ⟨hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
        rw [sep_push_body]; wp_steps; rw [add_24_add_8]; wp_done
      · intro s2 hpc2 hrun2 ⟨hpres2, hx19_2, hx20_2, hx21_2, hx22_2⟩
        have hrec := ih (cur + 24#64) s2 (memRegion cur 24 ∗ Frame)
          (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hpres2 hx19_2 hx20_2 hx21_2 hx22_2
        refine SepWP.strengthen_entails_const ?_ hrec
        have hsplit := cons_len_mul bs (bs2 :: tl2) 24
        have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
        exact Entails.refl _))

local macro "opt_proto_poly_encoder_main_steps " entry:term:max : tactic => `(tactic| (
  wp_init x s0; rcases x with ⟨a, optPb⟩
  dsimp only [DropOptProtoPolyEncoderGhost.a, DropOptProtoPolyEncoderGhost.optPb] at *
  nth_rw 1 [stackAt_dropStack64_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x23 v_w3 v_x22 v_x21 v_x20 v_x19
  have hfsp_align : ((s0.sp - 64#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 64#64 (by assumption) (by decide)
  cases optPb with
  | none =>
    rw [optProtoPolynomialEncoderAt_none]; dsimp only [optProtoPolynomialEncoderNoneTailSize]; wp_steps
    refine SepWP.focus_weaken (optProtoPolyEncoder_none_entails_memRegion_56 a) (by sep_focus) ?_
    refine SepWP.focus_weaken
      (stack_restore_64_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x23) v_w3 (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
    wp_done
  | some pb =>
    rw [optProtoPolynomialEncoderAt_some]
    refine SepWP.weaken_pre (sepConj_mono_left (protoPolyEncoderAt_entails_dealloc A a pb)) ?_
    wp_pull_exists; rename_i g; wp_focus_pure
    rintro ⟨hpts_le, hpts_cap_lt, hpts_ptr_ne, hpolys_le, hpolys_cap_lt, hpolys_ptr_ne⟩
    have hpts_cap_pow : g.pts.cap.toNat < 2 ^ 63 := by omega
    have hne_none := cap_add_one_beq_zero_false hpts_cap_pow
    refine seq_clean (mid := $entry + 88#64)
      (P_mid := (a ↦₆₄ g.pts.cap) ∗ ((a + 8#64) ↦₆₄ g.pts.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        (if g.pts.cap = 0 then emp
         else A.live g.pts.ptr (g.pts.cap.toNat * 24) 8 ∗ memRegion g.pts.ptr (g.pts.cap.toNat * 24)) ∗
        ((a + 24#64) ↦₆₄ g.polys.cap) ∗ ((a + 32#64) ↦₆₄ g.polys.ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
        (if g.polys.cap = 0 then emp
         else A.live g.polys.ptr (g.polys.cap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 g.polys.ptr pb.polys ∗
           memRegion (g.polys.ptr + BitVec.ofNat 64 (pb.polys.length * 24))
             ((g.polys.cap.toNat - pb.polys.length) * 24)) ∗
        memRegion (a + 48#64) 8 ∗ A.pool ∗ stackAt (s0.sp - 64#64) allocHookStack ∗
        (((s0.sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x23) ∗ ((s0.sp - 40#64) ↦₆₄ v_w3) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (Q := fun sm => Saved64Preserved s0 sm (s0.sp - 64#64) ∧
        sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.pts.ptr ∧ sm.readReg64 .x21 = g.pts.cap) ?_ ?_
    · generalize hxs : pb.pts = xs at hpts_le ⊢
      cases xs with
      | nil =>
        simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
          BitVec.add_zero, arrayAt, emp_sepConj]
        wp_steps; refine align_pre (by ac_rfl) ?_; wp_done
      | cons bs tl =>
        have hlen_pos : 0 < (bs :: tl).length := by simp
        have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
          have : (bs :: tl).length * 24 ≤ g.pts.cap.toNat * 24 := Nat.mul_le_mul_right 24 hpts_le; omega
        have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
        have hcap_ne : g.pts.cap ≠ 0 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
        simp only [hcap_ne, ↓reduceIte]
        refine seq_clean (mid := $entry + 64#64)
          (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 g.pts.ptr (bs :: tl) ∗
            A.pool ∗ stackAt (s0.sp - 64#64) allocHookStack ∗
            ((a ↦₆₄ g.pts.cap) ∗ ((a + 8#64) ↦₆₄ g.pts.ptr) ∗
             ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (bs :: tl).length) ∗
             A.live g.pts.ptr (g.pts.cap.toNat * 24) 8 ∗
             memRegion (g.pts.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24))
               ((g.pts.cap.toNat - (bs :: tl).length) * 24) ∗
             ((a + 24#64) ↦₆₄ g.polys.cap) ∗ ((a + 32#64) ↦₆₄ g.polys.ptr) ∗
             ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
             (if g.polys.cap = 0 then emp
              else A.live g.polys.ptr (g.polys.cap.toNat * 24) 8 ∗
                arrayAt (fun bs addr => vecU8 A addr bs) 24 g.polys.ptr pb.polys ∗
                memRegion (g.polys.ptr + BitVec.ofNat 64 (pb.polys.length * 24))
                  ((g.polys.cap.toNat - pb.polys.length) * 24)) ∗
             memRegion (a + 48#64) 8 ∗
             (((s0.sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
              ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x23) ∗ ((s0.sp - 40#64) ↦₆₄ v_w3) ∗
              ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
              ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
          (Q := fun sm => Saved64Preserved s0 sm (s0.sp - 64#64) ∧
            sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.pts.ptr ∧ sm.readReg64 .x21 = g.pts.cap ∧
            sm.readReg64 .x22 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x23 = g.pts.ptr + 8#64) ?_ ?_
        · wp_steps; refine align_pre (by ac_rfl) ?_; wp_done
        · intro s_loop hpc_loop hrun_loop ⟨hpres_loop, hx19_loop, hx20_loop, hx21_loop, hx22_loop, hx23_loop⟩
          refine SepWP.strengthen_entails_const ?_
            (hloop1 s0 (s0.sp - 64#64) a g.pts.ptr g.pts.cap hfsp_align (bs :: tl) g.pts.ptr s_loop _
              (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop
              hx19_loop hx20_loop hx21_loop hx22_loop hx23_loop)
          have hsplit : g.pts.cap.toNat * 24 =
              (bs :: tl).length * 24 + (g.pts.cap.toNat - (bs :: tl).length) * 24 := by
            rw [← Nat.add_mul]; congr 1; omega
          have hbound : (bs :: tl).length * 24 + (g.pts.cap.toNat - (bs :: tl).length) * 24 ≤ 2 ^ 64 := by
            rw [← hsplit]; omega
          conv_rhs =>
            arg 2; arg 2; arg 2; arg 1; arg 2
            rw [hsplit, ProofLib.memRegion_split g.pts.ptr ((bs :: tl).length * 24)
                  ((g.pts.cap.toNat - (bs :: tl).length) * 24) hbound]
          exact Entails.of_eq (by ac_rfl)
    · intro s1 hpc1 hrun1 ⟨⟨hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx20_1, hx21_1⟩
      refine seq_clean (mid := $entry + 112#64)
        (P_mid := (a ↦₆₄ g.pts.cap) ∗ ((a + 8#64) ↦₆₄ g.pts.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
          ((a + 24#64) ↦₆₄ g.polys.cap) ∗ ((a + 32#64) ↦₆₄ g.polys.ptr) ∗
          ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
          (if g.polys.cap = 0 then emp
           else A.live g.polys.ptr (g.polys.cap.toNat * 24) 8 ∗
             arrayAt (fun bs addr => vecU8 A addr bs) 24 g.polys.ptr pb.polys ∗
             memRegion (g.polys.ptr + BitVec.ofNat 64 (pb.polys.length * 24))
               ((g.polys.cap.toNat - pb.polys.length) * 24)) ∗
          memRegion (a + 48#64) 8 ∗ A.pool ∗ stackAt (s0.sp - 64#64) allocHookStack ∗
          (((s0.sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x23) ∗ ((s0.sp - 40#64) ↦₆₄ v_w3) ∗
           ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
        (Q := fun sm => Saved64Preserved s0 sm (s0.sp - 64#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
      · by_cases hc : g.pts.cap = 0
        · have hc_beq : (g.pts.cap == 0#64) = true := by rw [beq_iff_eq]; exact hc
          simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp] at hx21_1 ⊢; wp_steps; wp_done
        · have hc_beq : ¬((g.pts.cap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
          have hlsl := cap_mul_24 hpts_cap_lt
          simp only [hc, ↓reduceIte]; wp_steps
          wp_call hdealloc_raw (g.pts.ptr, g.pts.cap.toNat * 24, 8)
          refine align_pre (by rw [hsp_1]; ac_rfl) ?_; wp_done
      · intro s2 hpc2 hrun2 ⟨⟨hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
        refine seq_clean (mid := $entry + 164#64)
          (P_mid := (a ↦₆₄ g.pts.cap) ∗ ((a + 8#64) ↦₆₄ g.pts.ptr) ∗
            ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
            ((a + 24#64) ↦₆₄ g.polys.cap) ∗ ((a + 32#64) ↦₆₄ g.polys.ptr) ∗
            ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
            (if g.polys.cap = 0 then emp
             else A.live g.polys.ptr (g.polys.cap.toNat * 24) 8 ∗ memRegion g.polys.ptr (g.polys.cap.toNat * 24)) ∗
            memRegion (a + 48#64) 8 ∗ A.pool ∗ stackAt (s0.sp - 64#64) allocHookStack ∗
            (((s0.sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x23) ∗ ((s0.sp - 40#64) ↦₆₄ v_w3) ∗
             ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
          (Q := fun sm => Saved64Preserved s0 sm (s0.sp - 64#64) ∧
            sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.polys.ptr) ?_ ?_
        · generalize hys : pb.polys = ys at hpolys_le ⊢
          cases ys with
          | nil =>
            simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
              BitVec.add_zero, arrayAt, emp_sepConj]
            wp_steps; refine align_pre (by ac_rfl) ?_; wp_done
          | cons bs tl =>
            have hlen_pos : 0 < (bs :: tl).length := by simp
            have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
              have : (bs :: tl).length * 24 ≤ g.polys.cap.toNat * 24 := Nat.mul_le_mul_right 24 hpolys_le; omega
            have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
            have hcap_ne : g.polys.cap ≠ 0 := by intro hc0; rw [hc0] at hpolys_le; simp at hpolys_le
            simp only [hcap_ne, ↓reduceIte]
            refine seq_clean (mid := $entry + 140#64)
              (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 g.polys.ptr (bs :: tl) ∗
                A.pool ∗ stackAt (s0.sp - 64#64) allocHookStack ∗
                ((a ↦₆₄ g.pts.cap) ∗ ((a + 8#64) ↦₆₄ g.pts.ptr) ∗
                 ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
                 ((a + 24#64) ↦₆₄ g.polys.cap) ∗ ((a + 32#64) ↦₆₄ g.polys.ptr) ∗
                 ((a + 40#64) ↦₆₄ BitVec.ofNat 64 (bs :: tl).length) ∗
                 A.live g.polys.ptr (g.polys.cap.toNat * 24) 8 ∗
                 memRegion (g.polys.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24))
                   ((g.polys.cap.toNat - (bs :: tl).length) * 24) ∗
                 memRegion (a + 48#64) 8 ∗
                 (((s0.sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
                  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x23) ∗ ((s0.sp - 40#64) ↦₆₄ v_w3) ∗
                  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
              (Q := fun sm => Saved64Preserved s0 sm (s0.sp - 64#64) ∧
                sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.polys.ptr ∧
                sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = g.polys.ptr + 8#64) ?_ ?_
            · wp_steps; refine align_pre (by ac_rfl) ?_; wp_done
            · intro s_loop hpc_loop hrun_loop ⟨hpres_loop, hx19_loop, hx20_loop, hx21_loop, hx22_loop⟩
              refine SepWP.strengthen_entails_const ?_
                (hloop2 s0 (s0.sp - 64#64) a g.polys.ptr hfsp_align (bs :: tl) g.polys.ptr s_loop _
                  (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop
                  hx19_loop hx20_loop hx21_loop hx22_loop)
              have hsplit : g.polys.cap.toNat * 24 =
                  (bs :: tl).length * 24 + (g.polys.cap.toNat - (bs :: tl).length) * 24 := by
                rw [← Nat.add_mul]; congr 1; omega
              have hbound : (bs :: tl).length * 24 + (g.polys.cap.toNat - (bs :: tl).length) * 24 ≤ 2 ^ 64 := by
                rw [← hsplit]; omega
              conv_rhs =>
                arg 2; arg 2; arg 2; arg 2; arg 2; arg 2; arg 1; arg 2
                rw [hsplit, ProofLib.memRegion_split g.polys.ptr ((bs :: tl).length * 24)
                      ((g.polys.cap.toNat - (bs :: tl).length) * 24) hbound]
              exact Entails.of_eq (by ac_rfl)
        · intro s3 hpc3 hrun3 ⟨⟨hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3, hx20_3⟩
          by_cases hc : g.polys.cap = 0
          · have hc_beq : (g.polys.cap == 0#64) = true := by rw [beq_iff_eq]; exact hc
            simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp]; wp_steps
            refine SepWP.focus_weaken
              (protoPolyEncoderHeaders_entails_memRegion_56 a g.pts.cap g.pts.ptr
                (BitVec.ofNat 64 pb.pts.length) 0#64 g.polys.ptr (BitVec.ofNat 64 pb.polys.length)) (by sep_focus) ?_
            refine SepWP.focus_weaken
              (stack_restore_64_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
                (s0.readReg64 .x23) v_w3 (s0.readReg64 .x22) (s0.readReg64 .x21)
                (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
            wp_done
          · have hc_beq : ¬((g.polys.cap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
            have hlsl := cap_mul_24 hpolys_cap_lt
            simp only [hc, ↓reduceIte]; wp_steps
            refine SepWP.focus_weaken
              (protoPolyEncoderHeaders_entails_memRegion_56 a g.pts.cap g.pts.ptr
                (BitVec.ofNat 64 pb.pts.length) g.polys.cap g.polys.ptr (BitVec.ofNat 64 pb.polys.length)) (by sep_focus) ?_
            refine SepWP.focus_weaken
              (stack_restore_64_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
                (s0.readReg64 .x23) v_w3 (s0.readReg64 .x22) (s0.readReg64 .x21)
                (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
            rw [stackAt_dropStack64_split_bottom s0.sp]
            wp_call hdealloc_raw (g.polys.ptr, g.polys.cap.toNat * 24, 8)
            rw [← stackAt_dropStack64_split_bottom s0.sp]; wp_done))

private theorem drop_opt_proto_poly_encoder_body1 {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropOptProtoPolyEncoderName + bv% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::PolynomialEncoder>> [local#1]" "__rustc::__rust_dealloc")) (rustDeallocSpec A))
    (s0 : State) (fsp a ptsPtr ptsCap : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = (dropProgAtExt b ext).fnAddr dropOptProtoPolyEncoderName + 64#64 → s.status = .Running → Saved64Preserved s0 s fsp →
      s.readReg64 .x19 = a → s.readReg64 .x20 = ptsPtr → s.readReg64 .x21 = ptsCap →
      s.readReg64 .x22 = cnt → s.readReg64 .x23 = cur + 8#64 →
      SepWP (dropProgAtExt b ext) ((dropProgAtExt b ext).fnAddr dropOptProtoPolyEncoderName + 52#64) s
        (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved64Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = ptsPtr ∧
          sm.readReg64 .x21 = ptsCap ∧ sm.readReg64 .x22 = cnt ∧ sm.readReg64 .x23 = cur + 8#64) := by
  simp only [rustDeallocSpec] at hdealloc; dsimp only [dropProgAtExt, dropOptProtoPolyEncoderName, BitVec.ofNat_eq_ofNat] at *
  ls_code_fetches libsignalSessionCode spqrDropChainEpochBin b (Rust.withPanics ext) "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::PolynomialEncoder>> [local#1]"
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::PolynomialEncoder>> [local#1]" = entry
  examples_hide_fetches; opt_proto_poly_encoder_body1_steps (libsignalSessionCode.rebase b (Rust.withPanics ext)) entry

private theorem drop_opt_proto_poly_encoder_loop1 {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropOptProtoPolyEncoderName + bv% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::PolynomialEncoder>> [local#1]" "__rustc::__rust_dealloc")) (rustDeallocSpec A))
    (s0 : State) (fsp a ptsPtr ptsCap : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (dropProgAtExt b ext).fnAddr dropOptProtoPolyEncoderName + 64#64 → s.status = .Running → Saved64Preserved s0 s fsp →
      s.readReg64 .x19 = a → s.readReg64 .x20 = ptsPtr → s.readReg64 .x21 = ptsCap →
      s.readReg64 .x22 = BitVec.ofNat 64 rest.length → s.readReg64 .x23 = cur + 8#64 →
      SepWP (dropProgAtExt b ext) ((dropProgAtExt b ext).fnAddr dropOptProtoPolyEncoderName + 88#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved64Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = ptsPtr ∧ sm.readReg64 .x21 = ptsCap) := by
  have hbody := drop_opt_proto_poly_encoder_body1 (b := b) (ext := ext) hdealloc s0 fsp a ptsPtr ptsCap hfsp_align
  dsimp only [dropProgAtExt, dropOptProtoPolyEncoderName, BitVec.ofNat_eq_ofNat] at *
  ls_code_fetches libsignalSessionCode spqrDropChainEpochBin b (Rust.withPanics ext) "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::PolynomialEncoder>> [local#1]"
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::PolynomialEncoder>> [local#1]" = entry
  examples_hide_fetches; opt_proto_poly_encoder_loop1_steps entry

private theorem drop_opt_proto_poly_encoder_body2 {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropOptProtoPolyEncoderName + bv% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::PolynomialEncoder>> [local#1]" "__rustc::__rust_dealloc")) (rustDeallocSpec A))
    (s0 : State) (fsp a polysPtr : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = (dropProgAtExt b ext).fnAddr dropOptProtoPolyEncoderName + 140#64 → s.status = .Running → Saved64Preserved s0 s fsp →
      s.readReg64 .x19 = a → s.readReg64 .x20 = polysPtr → s.readReg64 .x21 = cnt → s.readReg64 .x22 = cur + 8#64 →
      SepWP (dropProgAtExt b ext) ((dropProgAtExt b ext).fnAddr dropOptProtoPolyEncoderName + 128#64) s
        (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved64Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = polysPtr ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
  simp only [rustDeallocSpec] at hdealloc; dsimp only [dropProgAtExt, dropOptProtoPolyEncoderName, BitVec.ofNat_eq_ofNat] at *
  ls_code_fetches libsignalSessionCode spqrDropChainEpochBin b (Rust.withPanics ext) "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::PolynomialEncoder>> [local#1]"
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::PolynomialEncoder>> [local#1]" = entry
  examples_hide_fetches; opt_proto_poly_encoder_body2_steps (libsignalSessionCode.rebase b (Rust.withPanics ext)) entry

private theorem drop_opt_proto_poly_encoder_loop2 {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropOptProtoPolyEncoderName + bv% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::PolynomialEncoder>> [local#1]" "__rustc::__rust_dealloc")) (rustDeallocSpec A))
    (s0 : State) (fsp a polysPtr : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (dropProgAtExt b ext).fnAddr dropOptProtoPolyEncoderName + 140#64 → s.status = .Running → Saved64Preserved s0 s fsp →
      s.readReg64 .x19 = a → s.readReg64 .x20 = polysPtr →
      s.readReg64 .x21 = BitVec.ofNat 64 rest.length → s.readReg64 .x22 = cur + 8#64 →
      SepWP (dropProgAtExt b ext) ((dropProgAtExt b ext).fnAddr dropOptProtoPolyEncoderName + 164#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved64Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = polysPtr) := by
  have hbody := drop_opt_proto_poly_encoder_body2 (b := b) (ext := ext) hdealloc s0 fsp a polysPtr hfsp_align
  dsimp only [dropProgAtExt, dropOptProtoPolyEncoderName, BitVec.ofNat_eq_ofNat] at *
  ls_code_fetches libsignalSessionCode spqrDropChainEpochBin b (Rust.withPanics ext) "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::PolynomialEncoder>> [local#1]"
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::PolynomialEncoder>> [local#1]" = entry
  examples_hide_fetches; opt_proto_poly_encoder_loop2_steps entry

theorem drop_glue_opt_proto_poly_encoder_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext) :
    subroutine_ok (dropProgAtExt b ext) ((dropProgAtExt b ext).fnAddr dropOptProtoPolyEncoderName) (dropOptProtoPolyEncoderSpec A) := by
  simp only [dropOptProtoPolyEncoderSpec]
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropOptProtoPolyEncoderName + bv% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::PolynomialEncoder>> [local#1]" "__rustc::__rust_dealloc")) (rustDeallocSpec A) :=
    sub_ok_of_addr_eq (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::PolynomialEncoder>> [local#1]" "__rustc::__rust_dealloc")) (b := b) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::PolynomialEncoder>> [local#1]") (ls_stub% "__rustc::__rust_dealloc") (by decide)) hdealloc
  have hloop1 := drop_opt_proto_poly_encoder_loop1 (b := b) (ext := ext) hdealloc_raw
  have hloop2 := drop_opt_proto_poly_encoder_loop2 (b := b) (ext := ext) hdealloc_raw
  ls_code_fetches libsignalSessionCode spqrDropChainEpochBin b (Rust.withPanics ext) "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::PolynomialEncoder>> [local#1]"
  dsimp only [dropProgAtExt, dropOptProtoPolyEncoderName, protoPolynomialEncoderSize, optProtoPolynomialEncoderNoneTailSize, BitVec.ofNat_eq_ofNat] at hloop1 hloop2 hdealloc_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::PolynomialEncoder>> [local#1]" = entry
  examples_hide_fetches; opt_proto_poly_encoder_main_steps entry

section PlacedOptProtoPolyEncoder
variable [LibsignalPlacement]

private theorem drop_opt_proto_poly_encoder_body1_placed {A : RustAlloc} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_132).rebase (blkPl_132).base H) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (fsp a ptsPtr ptsCap : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = (blkPl_132).base + 64#64 → s.status = .Running → Saved64Preserved s0 s fsp →
      s.readReg64 .x19 = a → s.readReg64 .x20 = ptsPtr → s.readReg64 .x21 = ptsCap →
      s.readReg64 .x22 = cnt → s.readReg64 .x23 = cur + 8#64 →
      SepWP ((blkPC_132).rebase (blkPl_132).base H) ((blkPl_132).base + 52#64) s
        (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved64Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = ptsPtr ∧
          sm.readReg64 .x21 = ptsCap ∧ sm.readReg64 .x22 = cnt ∧ sm.readReg64 .x23 = cur + 8#64) := by
  simp only [rustDeallocSpec] at hdealloc; opt_proto_poly_encoder_body1_steps ((blkPC_132).rebase (blkPl_132).base H) (blkPl_132).base

private theorem drop_opt_proto_poly_encoder_loop1_placed {A : RustAlloc} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_132).rebase (blkPl_132).base H) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (fsp a ptsPtr ptsCap : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (blkPl_132).base + 64#64 → s.status = .Running → Saved64Preserved s0 s fsp →
      s.readReg64 .x19 = a → s.readReg64 .x20 = ptsPtr → s.readReg64 .x21 = ptsCap →
      s.readReg64 .x22 = BitVec.ofNat 64 rest.length → s.readReg64 .x23 = cur + 8#64 →
      SepWP ((blkPC_132).rebase (blkPl_132).base H) ((blkPl_132).base + 88#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved64Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = ptsPtr ∧ sm.readReg64 .x21 = ptsCap) := by
  have hbody := drop_opt_proto_poly_encoder_body1_placed hdealloc s0 fsp a ptsPtr ptsCap hfsp_align
  opt_proto_poly_encoder_loop1_steps (blkPl_132).base

private theorem drop_opt_proto_poly_encoder_body2_placed {A : RustAlloc} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_132).rebase (blkPl_132).base H) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (fsp a polysPtr : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = (blkPl_132).base + 140#64 → s.status = .Running → Saved64Preserved s0 s fsp →
      s.readReg64 .x19 = a → s.readReg64 .x20 = polysPtr → s.readReg64 .x21 = cnt → s.readReg64 .x22 = cur + 8#64 →
      SepWP ((blkPC_132).rebase (blkPl_132).base H) ((blkPl_132).base + 128#64) s
        (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved64Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = polysPtr ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
  simp only [rustDeallocSpec] at hdealloc; opt_proto_poly_encoder_body2_steps ((blkPC_132).rebase (blkPl_132).base H) (blkPl_132).base

private theorem drop_opt_proto_poly_encoder_loop2_placed {A : RustAlloc} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_132).rebase (blkPl_132).base H) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (fsp a polysPtr : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (blkPl_132).base + 140#64 → s.status = .Running → Saved64Preserved s0 s fsp →
      s.readReg64 .x19 = a → s.readReg64 .x20 = polysPtr →
      s.readReg64 .x21 = BitVec.ofNat 64 rest.length → s.readReg64 .x22 = cur + 8#64 →
      SepWP ((blkPC_132).rebase (blkPl_132).base H) ((blkPl_132).base + 164#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved64Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = polysPtr) := by
  have hbody := drop_opt_proto_poly_encoder_body2_placed hdealloc s0 fsp a polysPtr hfsp_align
  opt_proto_poly_encoder_loop2_steps (blkPl_132).base

theorem drop_glue_opt_proto_poly_encoder_placed_ok {A : RustAlloc} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_132).rebase (blkPl_132).base H) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_132).rebase (blkPl_132).base H) (blkPl_132).base (dropOptProtoPolyEncoderSpec A) := by
  simp only [dropOptProtoPolyEncoderSpec]
  have hdealloc_raw := hdealloc
  have hloop1 := drop_opt_proto_poly_encoder_loop1_placed hdealloc_raw
  have hloop2 := drop_opt_proto_poly_encoder_loop2_placed hdealloc_raw
  dsimp only [protoPolynomialEncoderSize, optProtoPolynomialEncoderNoneTailSize] at *; opt_proto_poly_encoder_main_steps (blkPl_132).base

end PlacedOptProtoPolyEncoder

end CryptoVerification.SpqrV1.Drop
