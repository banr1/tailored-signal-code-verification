/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHooksPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Pure
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AddressA1Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSitesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.StrlenUtf8A1Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Read-Only `argv` Callee Specifications and Stub Contracts

Read-only (`↦ᵣ`) counterparts of `main`'s `argv`-consuming callee specifications (`strlenSpecRO`,
`fromUtf8AsciiSpecRO`, `memrchrSpecRO`, `addressSpecRO`), the Block-`617` callee bundle
`MainCalleesROBlk617`, address-space non-wrapping bounds on read-only slices, and `HookOk` /
placed stub discharges.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification
  (LibsignalHooks LibsignalPlacement ls_hook_ok_ultra_of_mem lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (subroutine_ok_rocl_of_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_plain withLsRoCl)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost UuidParser protocolAddressAt)
open CryptoVerification.SignalSession
  (CliHooks Utf8Ok cliExternsPlaced fromUtf8Hook lsFromUtf8Sym lsMemrchrSym memrchrHook
   strlenHook unmodelled)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkPC_617 blkPl_617 lsProg_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddressCall MemrchrCall addrParse cliExternsPlaced_fromUtf8 cliExternsPlaced_memrchr
   cliExternsPlaced_strlen lsHandleErrorSymMain memrchrIdx utf8Ok_of_ascii)
open CryptoVerification.SignalSession.Cli.Placed (lsProg_580)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (hookSat_withVmPreserved withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps
  (vmPreserved_setPC vmPreserved_setStatus vmPreserved_writeReg64)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget
  (AddressEnv reserve16Spec)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget
  (MainCalleesBlk617 tryAllocateInRustSpecOf)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced AllocContractsXCliPlaced)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget (doReserveSpecOf)

/-! ## Read-only callee specifications and `MainCalleesROBlk617` -/

/-- Read-only NUL-terminated byte slice `s` at `p` (`p ↦ᵣ (s ++ [0#8])`). -/
abbrev cStrAtRO (p : BitVec 64) (s : List (BitVec 8)) : SepProp :=
  p ↦ᵣ (s ++ [0#8])

/-- Read-only twin of `MainHops.strlenSpec`. -/
def strlenSpecRO (hookStack : Nat) : Spec (BitVec 64 × List (BitVec 8)) where
  pre := fun (p, s) s0 =>
    ⌜s0.readReg64 .x0 = p ∧ ∀ b ∈ s, b ≠ 0#8⌝ ∗ cStrAtRO p s ∗ stackAt s0.sp hookStack
  post := fun (p, s) s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 s.length ∧ sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ ∗
      cStrAtRO p s ∗ stackAt s0.sp hookStack

/-- Read-only twin of `MainHops.fromUtf8AsciiSpec`. -/
def fromUtf8AsciiSpecRO (hookStack : Nat) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (r, p, bs) s0 =>
    ⌜s0.readReg64 .x0 = p ∧ s0.readReg64 .x1 = BitVec.ofNat 64 bs.length ∧
      s0.readReg64 (.gpr 8#5) = r ∧ ∀ b ∈ bs, b.toNat < 128⌝ ∗
      (p ↦ᵣ bs) ∗ memRegion r 24 ∗ stackAt s0.sp hookStack
  post := fun (r, p, bs) s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ ∗ (p ↦ᵣ bs) ∗ (r ↦₆₄ 0#64) ∗
      ((r + 8#64) ↦₆₄ p) ∗ ((r + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      stackAt s0.sp hookStack

/-- Read-only twin of `MainHops.memrchrSpec`. -/
def memrchrSpecRO (stk : Nat) : Spec MemrchrCall where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = x.c ∧ s.readReg64 .x1 = x.p ∧
      s.readReg64 .x2 = BitVec.ofNat 64 x.bs.length ∧ x.bs.length < 2 ^ 64⌝ ∗
      (x.p ↦ᵣ x.bs) ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.fs = s0.fs ∧ match memrchrIdx x.c x.bs with
      | some i => sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 = BitVec.ofNat 64 i
      | none => sf.readReg64 .x0 = 0#64⌝ ∗ (x.p ↦ᵣ x.bs) ∗ stackAt s0.sp stk

/-- Read-only twin of `CalleesBudget.addressSpec`. -/
def addressSpecRO {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (uuidParse : UuidParser) (resStack : Nat) : Spec (AddressCall × M.σ) where
  pre := fun (x, st) s0 =>
    ⌜s0.readReg64 .x0 = x.out ∧ s0.readReg64 .x1 = x.p ∧
      s0.readReg64 .x2 = BitVec.ofNat 64 x.bs.length ∧
      FitsEnv M lim st (AddressEnv uuidParse x)⌝ ∗
      (x.p ↦ᵣ x.bs) ∗ memRegion x.out 32 ∗ A.pool lim st s0 ∗ stackAt s0.sp resStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ sf.fs = s0.fs ∧ AddressEnv uuidParse x evs⌝ ∗
        (x.p ↦ᵣ x.bs) ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp resStack ∗
        (match addrParse uuidParse x.bs with
         | none => (x.out ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (x.out + 8#64) 24
         | some a => ∃∗ g : AddrGhost,
             ⌜g.name.bytes = a.name ∧ g.name.cap = BitVec.ofNat 64 a.name.length ∧
               g.device = a.device⌝ ∗ protocolAddressAt A.repAlloc g x.out)

/-- Read-only-`argv` counterpart of `MainCalleesBlk617` on Block `617`. -/
structure MainCalleesROBlk617 [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (uuidParse : UuidParser) (hookStack resStack : Nat) : Prop where
  alloc : AllocContractsXCliPlaced A lim H
  allocFs : AllocContractsFsPlaced A lim H
  strlen : subroutine_ok (lsProg_617 H) (lsρ "strlen")
    (withLsRoCl lsmpl (withVmPreserved (strlenSpecRO hookStack)))
  fromUtf8 : subroutine_ok (lsProg_617 H) (lsρ lsFromUtf8Sym)
    (withLsRoCl lsmpl (withVmPreserved (fromUtf8AsciiSpecRO hookStack)))
  address : subroutine_ok (lsProg_617 H) (lsmpl.base 580)
    (withLsRoCl lsmpl (addressSpecRO A lim uuidParse resStack))
  reserve16 : subroutine_ok (lsProg_617 H) (lsmpl.base 561)
    (withLsRoCl lsmpl (reserve16Spec A lim resStack))
  reserve1 : subroutine_ok (lsProg_617 H) (lsmpl.base 561)
    (withLsRoCl lsmpl (doReserveSpecOf resStack A lim).keepsFs)
  tryAllocateIn3 : subroutine_ok (lsProg_617 H) (lsmpl.base 588)
    (withLsRoCl lsmpl (tryAllocateInRustSpecOf resStack A lim).keepsFs)
  handleErrorPanic :
    (lsProg_617 H).externAt? (lsρ lsHandleErrorSymMain) = some Rust.panicked

/-! ## Block `617` call-site projections -/

theorem main_panic_handle_error_ro_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {uuidParse : UuidParser} {hookStack resStack : Nat}
    (hc : MainCalleesROBlk617 A lim H uuidParse hookStack resStack) :
    ((blkPC_617).rebase (blkPl_617).base H).externAt? (lsρ lsHandleErrorSymMain) =
      some Rust.panicked :=
  hc.handleErrorPanic

theorem main_strlen_ro_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {uuidParse : UuidParser} {hookStack resStack : Nat}
    (hc : MainCalleesROBlk617 A lim H uuidParse hookStack resStack) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ "strlen")
      (withLsRoCl lsmpl (withVmPreserved (strlenSpecRO hookStack))) :=
  hc.strlen

theorem main_fromUtf8_ro_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {uuidParse : UuidParser} {hookStack resStack : Nat}
    (hc : MainCalleesROBlk617 A lim H uuidParse hookStack resStack) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsFromUtf8Sym)
      (withLsRoCl lsmpl (withVmPreserved (fromUtf8AsciiSpecRO hookStack))) :=
  hc.fromUtf8

theorem main_address_ro_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {uuidParse : UuidParser} {hookStack resStack : Nat}
    (hc : MainCalleesROBlk617 A lim H uuidParse hookStack resStack) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsmpl.base 580)
      (withLsRoCl lsmpl (addressSpecRO A lim uuidParse resStack)) :=
  hc.address

theorem address_ro_keepsFs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {uuidParse : UuidParser} {hookStack resStack : Nat}
    (hc : MainCalleesROBlk617 A lim H uuidParse hookStack resStack) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsmpl.base 580)
      (withLsRoCl lsmpl (addressSpecRO A lim uuidParse resStack).keepsFs) := by
  refine subroutine_ok_mono hc.address (fun _ _ _ hp => hp) (fun (x, st) R s1 sm hpost => ?_)
  dsimp only [withLsRoCl, Spec.keepsFs, addressSpecRO] at hpost ⊢
  refine Satisfies.mono (sepConj_mono_left (sepConj_mono_right ?_)) hpost
  refine Entails.sepExists_elim fun evs => ?_
  refine Entails.pure_left fun hpure => ?_
  refine Entails.pure_right hpure.2.1 ?_
  refine Entails.sepExists_right evs ?_
  exact Entails.pure_right hpure (Entails.refl _)

theorem main_reserve16_ro_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {uuidParse : UuidParser} {hookStack resStack : Nat}
    (hc : MainCalleesROBlk617 A lim H uuidParse hookStack resStack) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsmpl.base 561)
      (withLsRoCl lsmpl (reserve16Spec A lim resStack)) :=
  hc.reserve16

theorem main_reserve1_ro_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {uuidParse : UuidParser} {hookStack resStack : Nat}
    (hc : MainCalleesROBlk617 A lim H uuidParse hookStack resStack) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsmpl.base 561)
      (withLsRoCl lsmpl (doReserveSpecOf resStack A lim).keepsFs) :=
  hc.reserve1

theorem main_tryAllocateIn3_ro_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {uuidParse : UuidParser} {hookStack resStack : Nat}
    (hc : MainCalleesROBlk617 A lim H uuidParse hookStack resStack) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsmpl.base 588)
      (withLsRoCl lsmpl (tryAllocateInRustSpecOf resStack A lim).keepsFs) :=
  hc.tryAllocateIn3

/-! ## Read-only slice address-space bounds -/

theorem pointsToBytesRO_take_drop (ptr : BitVec 64) (n : Nat) (bs : List (BitVec 8))
    (hn : n ≤ bs.length) :
    (ptr ↦ᵣ bs) = (ptr ↦ᵣ bs.take n) ∗ ((ptr + BitVec.ofNat 64 n) ↦ᵣ bs.drop n) := by
  have h := pointsToBytesRO_append ptr (bs.take n) (bs.drop n)
  rw [List.take_append_drop, List.length_take_of_le hn] at h
  exact h

theorem pointsToBytesRO_focus8 (p : BitVec 64) {bs : List (BitVec 8)} {k : Nat}
    (hk : k < bs.length) :
    (p ↦ᵣ bs) =
      ((p + BitVec.ofNat 64 k) ↦₈ᵣ bs[k]) ∗
        ((p ↦ᵣ bs.take k) ∗ ((p + BitVec.ofNat 64 k + 1#64) ↦ᵣ bs.drop (k + 1))) := by
  rw [pointsToBytesRO_take_drop p k bs (Nat.le_of_lt hk),
    List.drop_eq_getElem_cons hk, pointsToBytesRO_cons]
  ac_nf

/-- Under `cStrAtRO p s` with no interior NUL byte, `s.length < 2 ^ 64` (otherwise the trailing NUL
at `p + s.length` wraps onto `s[(p + s.length - p).toNat] ≠ 0`). -/
theorem cStrAtRO_lt_addr_space {m : Memory} {p : BitVec 64} {s : List (BitVec 8)}
    {R : SepProp} (hno0 : ∀ b ∈ s, b ≠ 0#8) (hmem : m ⊨ cStrAtRO p s ∗ R) :
    s.length < 2 ^ 64 := by
  apply Classical.byContradiction
  intro hge
  let q : BitVec 64 := p + BitVec.ofNat 64 s.length
  let k : Nat := (q - p).toNat
  have hk2 : k < 2 ^ 64 := (q - p).isLt
  have hk : k < s.length := by omega
  have hpq : p + BitVec.ofNat 64 k = q := by
    dsimp only [k]
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    bv_arith
  have hmem1 : m ⊨ (q ↦₈ᵣ 0#8) ∗ ((p ↦ᵣ s) ∗ R) := by
    have h0 : m ⊨ ((p ↦ᵣ s) ∗ (q ↦₈ᵣ 0#8)) ∗ R := by
      dsimp only [cStrAtRO, q] at hmem ⊢
      rwa [pointsToBytesRO_append, pointsToBytesRO_singleton] at hmem
    ac_nf at h0 ⊢
  have hq0 : m.read8 q = 0#8 := (IsBlockRO.pointsTo8RO q 0#8).read hmem1
  have hmem2 : m ⊨ (q ↦₈ᵣ s[k]) ∗
      ((p ↦ᵣ s.take k) ∗ ((q + 1#64) ↦ᵣ s.drop (k + 1)) ∗ (q ↦₈ᵣ 0#8) ∗ R) := by
    have h0 : m ⊨ ((p ↦ᵣ s) ∗ (q ↦₈ᵣ 0#8)) ∗ R := by
      dsimp only [cStrAtRO, q] at hmem ⊢
      rwa [pointsToBytesRO_append, pointsToBytesRO_singleton] at hmem
    rw [pointsToBytesRO_focus8 p hk, hpq] at h0
    ac_nf at h0 ⊢
  have hqk : m.read8 q = s[k] := (IsBlockRO.pointsTo8RO q s[k]).read hmem2
  exact hno0 s[k] (List.getElem_mem hk) (hqk.symm.trans hq0)

private theorem read64_lo_eq_read8 (mem : Memory) (a : BitVec 64) :
    (mem.read64 a).setWidth 8 = mem.read8 a := by
  have h : (mem.read64 a).setWidth 8 = mem.read8 (a + 0#64) := by
    simp only [Memory.read64]
    generalize mem.read8 (a + 0#64) = x0
    generalize mem.read8 (a + 1#64) = x1
    generalize mem.read8 (a + 2#64) = x2
    generalize mem.read8 (a + 3#64) = x3
    generalize mem.read8 (a + 4#64) = x4
    generalize mem.read8 (a + 5#64) = x5
    generalize mem.read8 (a + 6#64) = x6
    generalize mem.read8 (a + 7#64) = x7
    bv_bits
  simpa only [BitVec.add_zero] using h

/-- Any `p ↦ᵣ bs` separated from an owned 8-byte read-write cell `r ↦₆₄ w0` has `bs.length < 2 ^ 64`
(otherwise `r` lies inside `[p, p + bs.length)` and writing a distinct byte to `r ↦₆₄ w0`
contradicts the preserved read-only byte `(r ↦₈ᵣ bs[(r - p).toNat])`). -/
theorem pointsToBytesRO_lt_addr_space_of_pointsTo64 {m : Memory} {p r w0 : BitVec 64}
    {bs : List (BitVec 8)} {R : SepProp}
    (hmem : m ⊨ (p ↦ᵣ bs) ∗ ((r ↦₆₄ w0) ∗ R)) :
    bs.length < 2 ^ 64 := by
  apply Classical.byContradiction
  intro hge
  let k : Nat := (r - p).toNat
  have hk2 : k < 2 ^ 64 := (r - p).isLt
  have hk : k < bs.length := by omega
  have hpr : p + BitVec.ofNat 64 k = r := by
    dsimp only [k]
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    bv_arith
  let Rest : SepProp := (p ↦ᵣ bs.take k) ∗ ((r + 1#64) ↦ᵣ bs.drop (k + 1)) ∗ R
  have h0 : m ⊨ (r ↦₆₄ w0) ∗ ((r ↦₈ᵣ bs[k]) ∗ Rest) := by
    have hm := hmem
    rw [pointsToBytesRO_focus8 p hk, hpr] at hm
    dsimp only [Rest]
    ac_nf at hm ⊢
  let v' : BitVec 64 := if bs[k] = 0#8 then 1#64 else 0#64
  have hw := IsBlock.write64 (IsBlock.pointsTo64 r w0) h0 v'
  have hr64 : (m.write64 r v').read64 r = v' := (IsBlock.pointsTo64 r v').read hw
  have hw' : m.write64 r v' ⊨ (r ↦₈ᵣ bs[k]) ∗ ((r ↦₆₄ v') ∗ Rest) := by
    ac_nf at hw ⊢
  have hr8 : (m.write64 r v').read8 r = bs[k] := (IsBlockRO.pointsTo8RO r bs[k]).read hw'
  have hlo := read64_lo_eq_read8 (m.write64 r v') r
  rw [hr64, hr8] at hlo
  by_cases hb : bs[k] = 0#8
  · simp [v', hb] at hlo
  · simp [v', hb] at hlo
    exact hb hlo.symm

theorem memRegion_24_words (r : BitVec 64) :
    memRegion r 24 =
      (∃∗ w0 : BitVec 64, r ↦₆₄ w0) ∗
      ((∃∗ w1 : BitVec 64, (r + 8#64) ↦₆₄ w1) ∗
       (∃∗ w2 : BitVec 64, (r + 16#64) ↦₆₄ w2)) := by
  rw [memRegion_split' (n := 8) (k := 16) rfl rfl (by decide),
    ProofLib.memRegion_eight r,
    memRegion_split' (b := r + 8#64) (n := 8) (k := 8) (b' := r + 16#64)
      rfl (by bv_omega) (by decide),
    ProofLib.memRegion_eight (r + 8#64),
    ProofLib.memRegion_eight (r + 16#64)]

theorem sliceRO_lt_addr_space_32 {m : Memory} {p out : BitVec 64} {bs : List (BitVec 8)}
    {R : SepProp} (h : m ⊨ (p ↦ᵣ bs) ∗ (memRegion out 32 ∗ R)) :
    bs.length < 2 ^ 64 := by
  rw [memRegion_split' (b := out) (n := 8) (k := 24) rfl rfl (by decide),
    ProofLib.memRegion_eight out] at h
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    satisfies_sepExists] at h
  rcases h with ⟨w0, hw⟩
  have hw' : m ⊨ (p ↦ᵣ bs) ∗ ((out ↦₆₄ w0) ∗ (memRegion (out + 8#64) 24 ∗ R)) := by
    ac_nf at hw ⊢
  exact pointsToBytesRO_lt_addr_space_of_pointsTo64 hw'

/-! ## `HookOk` discharges for `strlenHook`, `fromUtf8Hook`, and `memrchrHook` -/

private theorem hookOk_of_eq_retHook {α : Type} {h : State → State} {spec : Spec α}
    (f : α → State → State)
    (heq : ∀ x R s0, s0.status = .Running → (s0.mem ⊨ spec.pre x s0 ∗ R) →
      h s0 = retHook (f x) s0)
    (hok : ∀ x, HookOk (retHook (f x))
      { pre := fun (_ : Unit) => spec.pre x
        post := fun _ => spec.post x
        onPanic := fun _ => spec.onPanic x
        onExit := fun _ => spec.onExit x
        onOom := fun _ => spec.onOom x }) :
    HookOk h spec := by
  intro x R s0 hrun hpre hsp
  rw [heq x R s0 hrun hpre]
  exact hok x () R s0 hrun hpre hsp

private theorem getD_append_right_zero (s : List (BitVec 8)) :
    (s ++ [0#8]).getD s.length 0#8 = 0#8 := by
  simp [List.getD]

private theorem getD_append_left {s : List (BitVec 8)} {m : Nat} (hm : m < s.length) :
    (s ++ [0#8]).getD m 0#8 = s[m] := by
  simp [List.getD, List.getElem?_append_left hm, hm]

theorem strlenHook_ro_ok (hookStack : Nat) : HookOk strlenHook (strlenSpecRO hookStack) := by
  refine hookOk_of_eq_retHook (fun (_, s) st => st.writeReg64 .x0 (BitVec.ofNat 64 s.length))
    (fun ⟨p, s⟩ R s0 _hrun hpre => ?_) (fun ⟨p, s⟩ => ?_)
  · simp only [strlenSpecRO, sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨⟨hx0, hno0⟩, hmem⟩
    have hs_lt : s.length < 2 ^ 64 := cStrAtRO_lt_addr_space hno0 hmem
    have hlen : (s ++ [0#8]).length ≤ 2 ^ 64 := by simp; omega
    have hmem' : s0.mem ⊨ (p ↦ᵣ (s ++ [0#8])) ∗ (stackAt s0.sp hookStack ∗ R) := hmem
    have hread : s0.mem.readBytes p (s ++ [0#8]).length = s ++ [0#8] :=
      (IsBlockRO.pointsToBytesRO p (s ++ [0#8]) hlen).read hmem'
    have hcan0 : s0.mem.canRead p (s ++ [0#8]).length = true :=
      (IsBlockRO.pointsToBytesRO p (s ++ [0#8]) hlen).canRead hlen hmem'
    have hcan : s0.mem.canRead p (s.length + 1) = true := by simpa using hcan0
    have hnul : s0.mem.read8 (p + BitVec.ofNat 64 s.length) = 0#8 := by
      rw [Memory.read8_of_readBytes s0.mem p (s ++ [0#8]) hread s.length (by simp)]
      exact getD_append_right_zero s
    have hex : ∃ n, s0.mem.canRead p (n + 1) = true ∧
        s0.mem.read8 (p + BitVec.ofNat 64 n) = 0#8 :=
      ⟨s.length, hcan, hnul⟩
    have hfind : Nat.find hex = s.length := by
      refine (Nat.find_eq_iff hex).mpr ⟨⟨hcan, hnul⟩, fun m hm ⟨_, hm0⟩ => ?_⟩
      rw [Memory.read8_of_readBytes s0.mem p (s ++ [0#8]) hread m (by simp; omega),
        getD_append_left hm] at hm0
      exact hno0 s[m] (List.getElem_mem hm) hm0
    unfold strlenHook
    dsimp only
    simp only [hx0, hex, ↓reduceDIte, hfind]
  · refine retHook_ok fun _ R s0 hrun hpre _hsp => ?_
    simp only [strlenSpecRO, sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨_, hmem⟩
    refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl, hrun,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    simp only [strlenSpecRO, retHook, State.setPC, State.writeReg64, State.readReg64,
      sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨rfl, trivial, trivial⟩, hmem⟩

theorem fromUtf8Hook_ro_ok (hookStack : Nat) (err : List (BitVec 8) → BitVec 64 × BitVec 16) :
    HookOk (fromUtf8Hook err) (fromUtf8AsciiSpecRO hookStack) := by
  refine hookOk_of_eq_retHook
    (fun (r, p, bs) st =>
      st.setMem (((st.mem.write64 r 0#64).write64 (r + 8#64) p).write64
        (r + 16#64) (BitVec.ofNat 64 bs.length)))
    (fun ⟨r, p, bs⟩ R s0 _hrun hpre => ?_) (fun ⟨r, p, bs⟩ => ?_)
  · simp only [fromUtf8AsciiSpecRO, sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨⟨hx0, hx1, hx8, hascii⟩, hmem⟩
    have hbs_lt : bs.length < 2 ^ 64 := by
      have hm := hmem
      rw [memRegion_24_words r] at hm
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
        satisfies_sepExists] at hm
      rcases hm with ⟨w2, w1, w0, hw⟩
      have hw' : s0.mem ⊨ (p ↦ᵣ bs) ∗
          ((r ↦₆₄ w0) ∗ (((r + 8#64) ↦₆₄ w1) ∗ (((r + 16#64) ↦₆₄ w2) ∗ (stackAt s0.sp hookStack ∗ R)))) := by
        ac_nf at hw ⊢
      exact pointsToBytesRO_lt_addr_space_of_pointsTo64 hw'
    have hbs_le : bs.length ≤ 2 ^ 64 := Nat.le_of_lt hbs_lt
    have hread : s0.mem.readBytes p bs.length = bs :=
      (IsBlockRO.pointsToBytesRO p bs hbs_le).read hmem
    have hcanR : s0.mem.canRead p bs.length = true :=
      (IsBlockRO.pointsToBytesRO p bs hbs_le).canRead hbs_le hmem
    have hmemR : s0.mem ⊨ memRegion r 24 ∗ ((p ↦ᵣ bs) ∗ (stackAt s0.sp hookStack ∗ R)) := by
      ac_nf at hmem ⊢
    have hcanW : s0.mem.canWrite r 24 = true :=
      (IsBlock.memRegion r 24).canWrite (by decide) hmemR
    have hlen_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbs_lt]
    have hutf8 : Utf8Ok bs := utf8Ok_of_ascii hascii
    change fromUtf8Hook err s0 = _
    unfold fromUtf8Hook
    have hx8' : s0.readReg64 .x8 = r := hx8
    dsimp only
    rw [hx0, hx1, hx8', hlen_nat, hcanR, hcanW, hread]
    simp only [Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hutf8]
  · refine retHook_ok fun _ R s0 hrun hpre _hsp => ?_
    simp only [fromUtf8AsciiSpecRO, sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨_, hmem⟩
    rw [memRegion_24_words r] at hmem
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      satisfies_sepExists] at hmem
    rcases hmem with ⟨w2, w1, w0, hw⟩
    let F : SepProp := (p ↦ᵣ bs) ∗ (stackAt s0.sp hookStack ∗ R)
    have h0 : s0.mem ⊨ (r ↦₆₄ w0) ∗ (((r + 8#64) ↦₆₄ w1) ∗ (((r + 16#64) ↦₆₄ w2) ∗ F)) := by
      dsimp only [F]; ac_nf at hw ⊢
    have hkf1 : s0.mem.KeepsFrozen (s0.mem.write64 r 0#64) :=
      Memory.keepsFrozen_write64 ((IsBlock.pointsTo64 r w0).canWrite (by decide) h0) 0#64
    have hw1 := IsBlock.write64 (IsBlock.pointsTo64 r w0) h0 0#64
    have h1 : s0.mem.write64 r 0#64 ⊨
        ((r + 8#64) ↦₆₄ w1) ∗ (((r + 16#64) ↦₆₄ w2) ∗ ((r ↦₆₄ 0#64) ∗ F)) := by
      ac_nf at hw1 ⊢
    have hkf2 : s0.mem.KeepsFrozen ((s0.mem.write64 r 0#64).write64 (r + 8#64) p) :=
      hkf1.trans
        (Memory.keepsFrozen_write64 ((IsBlock.pointsTo64 (r + 8#64) w1).canWrite (by decide) h1) p)
    have hw2 := IsBlock.write64 (IsBlock.pointsTo64 (r + 8#64) w1) h1 p
    have h2 : (s0.mem.write64 r 0#64).write64 (r + 8#64) p ⊨
        ((r + 16#64) ↦₆₄ w2) ∗ ((r ↦₆₄ 0#64) ∗ (((r + 8#64) ↦₆₄ p) ∗ F)) := by
      ac_nf at hw2 ⊢
    have hkf3 : s0.mem.KeepsFrozen
        (((s0.mem.write64 r 0#64).write64 (r + 8#64) p).write64
          (r + 16#64) (BitVec.ofNat 64 bs.length)) :=
      hkf2.trans (Memory.keepsFrozen_write64
        ((IsBlock.pointsTo64 (r + 16#64) w2).canWrite (by decide) h2)
        (BitVec.ofNat 64 bs.length))
    have hw3 := IsBlock.write64 (IsBlock.pointsTo64 (r + 16#64) w2) h2 (BitVec.ofNat 64 bs.length)
    refine ⟨hkf3, rfl, hrun,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    dsimp only [fromUtf8AsciiSpecRO, State.setMem]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨rfl, rfl⟩, ?_⟩
    dsimp only [F] at hw3
    ac_nf at hw3 ⊢

theorem memrchrHook_ro_ok (stk : Nat) : HookOk memrchrHook (memrchrSpecRO stk) := by
  intro x R s0 hrun hpre _hsp
  simp only [memrchrSpecRO, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hlt⟩, hmem⟩
  have hlen : (s0.readReg64 .x2).toNat = x.bs.length := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  have hlen_le : x.bs.length ≤ 2 ^ 64 := Nat.le_of_lt hlt
  have hrd : s0.mem.readBytes x.p x.bs.length = x.bs :=
    (IsBlockRO.pointsToBytesRO x.p x.bs hlen_le).read hmem
  have hcan : s0.mem.canRead x.p x.bs.length = true :=
    (IsBlockRO.pointsToBytesRO x.p x.bs hlen_le).canRead hlen_le hmem
  have hmemrchr :
      memrchrHook s0 =
        match memrchrIdx x.c x.bs with
        | some i => retHook (fun s => (s.writeReg64 .x0 1#64).writeReg64 .x1 (BitVec.ofNat 64 i)) s0
        | none => retHook (fun s => s.writeReg64 .x0 0#64) s0 := by
    unfold memrchrHook memrchrIdx
    simp only [hx0, hx1, hlen, hcan, hrd, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rfl
  rw [hmemrchr]
  cases hidx : memrchrIdx x.c x.bs with
  | some i =>
    refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
    dsimp only [memrchrSpecRO]
    simp only [hidx, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨by simp only [retHook, arm64_norm],
      by simp only [retHook, arm64_norm],
      ⟨by simp only [retHook, arm64_norm], by simp only [retHook, arm64_norm]⟩⟩, hmem⟩
  | none =>
    refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
    dsimp only [memrchrSpecRO]
    simp only [hidx, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨by simp only [retHook, arm64_norm],
      by simp only [retHook, arm64_norm],
      by simp only [retHook, arm64_norm]⟩, hmem⟩

private theorem vmPreserved_setMem_of_perm_eq {s : State} {m' : Memory}
    (hp : m'.perm = s.mem.perm) :
    VmPreserved s (s.setMem m') := by
  cases s
  exact ⟨⟨rfl, rfl, rfl⟩, rfl, fun a => congrFun hp a, fun _ _ _ => rfl⟩

theorem strlenHook_vmPreserved (s : State) : VmPreserved s (strlenHook s) := by
  unfold strlenHook
  dsimp only
  split
  · unfold retHook
    simp only [vmPreserved_setPC, vmPreserved_writeReg64, VmPreserved.refl]
  · unfold unmodelled
    simp only [vmPreserved_setStatus, VmPreserved.refl]

theorem fromUtf8Hook_vmPreserved (err : List (BitVec 8) → BitVec 64 × BitVec 16) (s : State) :
    VmPreserved s (fromUtf8Hook err s) := by
  unfold fromUtf8Hook
  dsimp only
  split
  · unfold unmodelled
    simp only [vmPreserved_setStatus, VmPreserved.refl]
  · split
    · unfold retHook
      rw [vmPreserved_setPC]
      exact vmPreserved_setMem_of_perm_eq (by
        rw [Memory.perm_write64, Memory.perm_write64, Memory.perm_write64])
    · unfold retHook
      rw [vmPreserved_setPC]
      exact vmPreserved_setMem_of_perm_eq (by
        rw [Memory.perm_write16, Memory.perm_write64, Memory.perm_write64])

theorem memrchrHook_vmPreserved (s : State) : VmPreserved s (memrchrHook s) := by
  unfold memrchrHook
  change VmPreserved s
    (if (!s.mem.canRead (s.readReg64 .x1) (s.readReg64 .x2).toNat) = true then
      unmodelled "memrchr: unreadable bytes" s
    else
      match ((List.range (s.mem.readBytes (s.readReg64 .x1) (s.readReg64 .x2).toNat).length).filter
        fun i => (s.mem.readBytes (s.readReg64 .x1) (s.readReg64 .x2).toNat)[i]? ==
          some ((s.readReg64 .x0).setWidth 8)).getLast? with
      | some i => retHook (fun s => (s.writeReg64 .x0 1#64).writeReg64 .x1 (BitVec.ofNat 64 i)) s
      | none => retHook (fun s => s.writeReg64 .x0 0#64) s)
  split
  · unfold unmodelled
    simp only [vmPreserved_setStatus, VmPreserved.refl]
  · split
    · unfold retHook
      simp only [vmPreserved_setPC, vmPreserved_writeReg64, VmPreserved.refl]
    · unfold retHook
      simp only [vmPreserved_setPC, vmPreserved_writeReg64, VmPreserved.refl]

/-! ## Placed stub discharges and `cliExternsPlaced` lookups -/

private theorem subroutine_ok_rocl_of_plain [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withLsRoCl lsmpl spec) :=
  subroutine_ok_rocl_of_withLsCodeRoLoaded (subroutine_ok_withLsCodeRoLoaded_of_plain h)

theorem strlen_ro_placed_ok_of_hooks [LibsignalPlacement]
    {H : LibsignalHooks} {hookStack : Nat}
    (hext : H "strlen" = some strlenHook) :
    subroutine_ok (lsProg_617 H) (lsρ "strlen")
      (withLsRoCl lsmpl (withVmPreserved (strlenSpecRO hookStack))) := by
  have hsat : HookSat H "strlen" (strlenSpecRO hookStack) :=
    ⟨strlenHook, hext, strlenHook_ro_ok hookStack⟩
  have hsat_vm : HookSat H "strlen" (withVmPreserved (strlenSpecRO hookStack)) :=
    hookSat_withVmPreserved hsat (fun f hf s => by
      cases hext.symm.trans hf
      exact strlenHook_vmPreserved s)
  exact subroutine_ok_rocl_of_plain
    (ls_hook_ok_ultra_of_mem (prog := lsProg_617 H) (i := 617) hsat_vm (by decide))

theorem strlen_ro_placed_ok_cliExterns [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (W : CliHooks) (hookStack : Nat) :
    subroutine_ok (lsProg_617 (cliExternsPlaced mmpl W)) (lsρ "strlen")
      (withLsRoCl lsmpl (withVmPreserved (strlenSpecRO hookStack))) :=
  strlen_ro_placed_ok_of_hooks (cliExternsPlaced_strlen mmpl W)

theorem fromUtf8Ascii_ro_placed_ok_of_hooks [LibsignalPlacement]
    {H : LibsignalHooks} {hookStack : Nat}
    {err : List (BitVec 8) → BitVec 64 × BitVec 16}
    (hext : H lsFromUtf8Sym = some (fromUtf8Hook err)) :
    subroutine_ok (lsProg_617 H) (lsρ lsFromUtf8Sym)
      (withLsRoCl lsmpl (withVmPreserved (fromUtf8AsciiSpecRO hookStack))) := by
  have hsat : HookSat H lsFromUtf8Sym (fromUtf8AsciiSpecRO hookStack) :=
    ⟨fromUtf8Hook err, hext, fromUtf8Hook_ro_ok hookStack err⟩
  have hsat_vm : HookSat H lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpecRO hookStack)) :=
    hookSat_withVmPreserved hsat (fun f hf s => by
      cases hext.symm.trans hf
      exact fromUtf8Hook_vmPreserved err s)
  exact subroutine_ok_rocl_of_plain
    (ls_hook_ok_ultra_of_mem (prog := lsProg_617 H) (i := 617) hsat_vm (by decide))

theorem fromUtf8Ascii_ro_placed_ok_cliExterns [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (W : CliHooks) (hookStack : Nat) :
    subroutine_ok (lsProg_617 (cliExternsPlaced mmpl W)) (lsρ lsFromUtf8Sym)
      (withLsRoCl lsmpl (withVmPreserved (fromUtf8AsciiSpecRO hookStack))) :=
  fromUtf8Ascii_ro_placed_ok_of_hooks (cliExternsPlaced_fromUtf8 mmpl W)

theorem memrchr_ro_blk580_ok_of_hooks [LibsignalPlacement]
    {H : LibsignalHooks} {stk : Nat}
    (hext : H lsMemrchrSym = some memrchrHook) :
    subroutine_ok (lsProg_580 H) (lsρ lsMemrchrSym)
      (withLsRoCl lsmpl (withVmPreserved (memrchrSpecRO stk))) := by
  have hsat : HookSat H lsMemrchrSym (memrchrSpecRO stk) :=
    ⟨memrchrHook, hext, memrchrHook_ro_ok stk⟩
  have hsat_vm : HookSat H lsMemrchrSym (withVmPreserved (memrchrSpecRO stk)) :=
    hookSat_withVmPreserved hsat (fun f hf s => by
      cases hext.symm.trans hf
      exact memrchrHook_vmPreserved s)
  have hplain : subroutine_ok (lsProg_580 H) (lsρ lsMemrchrSym)
      (withVmPreserved (memrchrSpecRO stk)) := by
    dsimp only [lsProg_580]
    exact ls_hook_ok_ultra_of_mem hsat_vm (by decide)
  exact subroutine_ok_rocl_of_plain hplain

theorem memrchr_ro_blk580_ok_cliExterns [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (W : CliHooks) (stk : Nat) :
    subroutine_ok (lsProg_580 (cliExternsPlaced mmpl W)) (lsρ lsMemrchrSym)
      (withLsRoCl lsmpl (withVmPreserved (memrchrSpecRO stk))) :=
  memrchr_ro_blk580_ok_of_hooks (cliExternsPlaced_memrchr mmpl W)

/-! ## `MainCalleesROBlk617` assembly -/

theorem mainCalleesROBlk617_of_mainCalleesBlk617_and_addr [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {uuidParse : UuidParser} {hookStack resStack : Nat}
    {err : List (BitVec 8) → BitVec 64 × BitVec 16}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hstrlen : H "strlen" = some strlenHook)
    (hutf8 : H lsFromUtf8Sym = some (fromUtf8Hook err))
    (haddr : subroutine_ok (lsProg_617 H) (lsmpl.base 580)
      (withLsRoCl lsmpl (addressSpecRO A lim uuidParse resStack))) :
    MainCalleesROBlk617 A lim H uuidParse hookStack resStack where
  alloc := hc.alloc
  allocFs := hc.allocFs
  strlen := strlen_ro_placed_ok_of_hooks hstrlen
  fromUtf8 := fromUtf8Ascii_ro_placed_ok_of_hooks hutf8
  address := haddr
  reserve16 := hc.reserve16
  reserve1 := hc.reserve1
  tryAllocateIn3 := hc.tryAllocateIn3
  handleErrorPanic := hc.handleErrorPanic

end LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO
