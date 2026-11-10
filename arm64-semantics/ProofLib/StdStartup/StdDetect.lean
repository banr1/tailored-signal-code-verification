/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.WP.StepsProcess
public import ProofLib.StdStartup.StackInit
public import ProofLib.StdStartup.Layout
public import ProofLib.StdStartup.MemOps
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics
import Arm64.Trusted.Spec.Hoare

/-!
# `libc_start_init` and LSE Initialization Contracts

Symbolic `SepWP` contracts for `libc_start_main_stage2` entry, `libc_start_init`, `_init`,
`getauxval`, `detect_and_initialize`, `RUST_LSE_INIT::init_lse`, and `__do_init` under
`hwcap &&& 0x3#64 = 0x3#64`.
-/
set_option autoImplicit false
@[expose] public section
namespace ProofLib.StdStartup
open Arm64 Arm64.Obj ProofLib

@[inline] def decodeWord (w : BitVec 32) : Instr := (Arm64.decode w).getD (.udf 0#16)
@[inline] def decodeWords (ws : List (BitVec 32)) : List Instr := ws.map decodeWord
theorem StdStatePreserved.of_processFields {s0 sf : State} (h : ProcessFieldsPreserved s0 sf) : StdStatePreserved s0 sf := h

/-- Exact 4-instruction word list for `_init` (`stp; mov; ldp; ret`). -/
def initFnWords : List (BitVec 32) := [0xa9bf7bfd#32, 0x910003fd#32, 0xa8c17bfd#32, 0xd65f03c0#32]

/-- Parametric 14-instruction list for `__do_init` at `L.doInitAddr`. -/
def doInitInstrs (L : StdBinaryLayout) : List Instr :=
  let objAddr := (L.initializedAddr + 15#64) &&& ~~~15#64
  [ .adr true (.gpr 1#5) (adrpOff L.doInitAddr L.initializedAddr), .ldr .W32 .B8 false (.gpr 0#5) (.Offset (.gpr 1#5) (pageLo12 L.initializedAddr)),
    decodeWord 0x35000160#32, .adr true (.gpr 0#5) (adrpOff (L.doInitAddr + 0x0c#64) (L.gotAddr + 0x30#64)), decodeWord 0x52800022#32,
    .str .B8 (.gpr 2#5) (.Offset (.gpr 1#5) (pageLo12 L.initializedAddr)), .ldr .W64 .X64 false (.gpr 0#5) (.Offset (.gpr 0#5) (pageLo12 (L.gotAddr + 0x30#64))),
    decodeWord 0xb40000c0#32, .adr true (.gpr 1#5) (adrpOff (L.doInitAddr + 0x20#64) objAddr), .adr true (.gpr 0#5) (adrpOff (L.doInitAddr + 0x24#64) 0#64),
    .addSubImm .W64 .ADD (.gpr 1#5) (.gpr 1#5) (objAddr.truncate 12) false, decodeWord 0x91000000#32, decodeWord 0x14000001#32, decodeWord 0xd65f03c0#32 ]

/-- Parametric 25-instruction list for `getauxval` at `L.getauxvalAddr`. -/
def getauxvalInstrs (L : StdBinaryLayout) : List Instr :=
  decodeWords [0xa9be7bfd#32, 0xf1005c1f#32, 0x910003fd#32, 0xf9000bf3#32, 0x54000120#32] ++
  [ .adr true (.gpr 1#5) (adrpOff (L.getauxvalAddr + 0x14#64) (L.libcAddr + 0x08#64)), .ldr .W64 .X64 false (.gpr 1#5) (.Offset (.gpr 1#5) (pageLo12 (L.libcAddr + 0x08#64))) ] ++
  decodeWords [0xf9400033#32, 0xeb00027f#32, 0xb4000133#32, 0x540000c0#32, 0x91004021#32, 0x17fffffb#32] ++
  [ .adr true (.gpr 0#5) (adrpOff (L.getauxvalAddr + 0x34#64) (L.libcAddr + 0x02#64)), .ldr .W32 .B8 false (.gpr 19#5) (.Offset (.gpr 0#5) (pageLo12 (L.libcAddr + 0x02#64))) ] ++
  decodeWords [0x14000006#32, 0xf9400433#32, 0x14000004#32] ++ [ .bl (L.errnoLocationAddr - (L.getauxvalAddr + 0x48#64)) ] ++
  decodeWords [0x52800041#32, 0xb9000001#32, 0xaa1303e0#32, 0xf9400bf3#32, 0xa8c27bfd#32, 0xd65f03c0#32]

def detectChunk1Words : List (BitVec 32) := [0x52800088#32, 0xf277027f#32, 0x5280008a#32, 0x72a00208#32, 0x2a3303e9#32, 0x53037e6b#32, 0x9a88014a#32, 0x72000268#32, 0x92773929#32, 0x9a9f114a#32, 0xf269c93f#32, 0x53017e6c#32, 0xb26f0149#32, 0xd350fc0d#32, 0x5319666e#32, 0x9a8a012a#32, 0x52800029#32, 0xd2a80010#32, 0x6a53653f#32, 0x52a8000f#32, 0xf2c00030#32, 0x121f016b#32, 0x121a018c#32, 0x9a8f120f#32, 0x926101ad#32, 0xd3607dce#32, 0xaa0c016b#32, 0xaa0f01ac#32, 0x7218027f#32, 0xaa0b014a#32, 0x9a8e118b#32, 0xf271027f#32, 0x0a533508#32, 0xaa0b014a#32, 0xd34e3a6e#32, 0xd34bfc11#32, 0xb258014b#32, 0xb258054c#32, 0xb258094d#32, 0x9a8b014b#32, 0x9a8c014c#32, 0xf271027f#32, 0x9a8d014a#32, 0xf252001f#32, 0x5318626d#32, 0x9a8a018a#32, 0x7206027f#32, 0xd374cc0c#32, 0x9a8a016a#32, 0x531b6e6b#32, 0x72001d1f#32]
def detectChunk2Words : List (BitVec 32) := [0xaa0d214a#32, 0x926d018c#32, 0x5280004d#32, 0x121b0a72#32, 0xd36bac03#32, 0x53155661#32, 0xaa0b494a#32, 0x531c726b#32, 0xaa0c014a#32, 0x531d766c#32, 0xaa0bed4a#32, 0x531e7a6b#32, 0xaa0cb14a#32, 0x531f7e6c#32, 0xaa0b914a#32, 0x5310426b#32, 0xaa0c954a#32, 0x5310400c#32, 0xaa0b254a#32, 0x1200000b#32, 0xaa0b294a#32, 0xd34cfc0b#32, 0xaa0c9d4a#32, 0x5312480c#32, 0x927b016b#32, 0xaa0b014a#32, 0x530c326b#32, 0xaa0c8d4a#32, 0x53165a6c#32, 0xb2630148#32, 0x9a880148#32, 0x5314526a#32, 0x6a40393f#32, 0xaa0bad08#32, 0x5308200b#32, 0xaa0a2d08#32, 0x530d340a#32, 0xaa0b6908#32, 0x53011c0b#32, 0xaa0a7108#32, 0xb27c0109#32, 0x9a881128#32, 0x721f027f#32, 0x92770669#32, 0x1a9f17ea#32, 0xf108013f#32, 0x2a330149#32, 0x1a9f07ea#32, 0x7200013f#32, 0x0a0c0169#32, 0xaa0a010b#32, 0x1a8a13ea#32]
def detectChunk3Words : List (BitVec 32) := [0x9a8b110b#32, 0x6a09015f#32, 0xb2700170#32, 0x9a8d05a8#32, 0xf25c001f#32, 0xd356fe6d#32, 0x9a9f150f#32, 0x6a090148#32, 0x9a9f11e9#32, 0x6a0e015f#32, 0xd34afc0e#32, 0x9a8b120b#32, 0x6a0d015f#32, 0x5305166f#32, 0xb241016d#32, 0x0a0e018e#32, 0x0a11018c#32, 0x9a8b11ad#32, 0x6a0e015f#32, 0xd351fe70#32, 0xb27301ae#32, 0x53061a6b#32, 0x9a8d11cd#32, 0x53030e6e#32, 0x6a0c015f#32, 0xb27201ac#32, 0x0a521571#32, 0xd352fe72#32, 0x9a8d118d#32, 0x0a1001ec#32, 0x6a0e015f#32, 0xb27d01af#32, 0x0a535590#32, 0x9a8d11ef#32, 0x6a11015f#32, 0xd3534e6d#32, 0xb25301f1#32, 0x0a0b0210#32, 0x9a8f122f#32, 0x6a10015f#32, 0x0a1201b2#32, 0xb25201f0#32, 0x53124a71#32, 0x9a8f120f#32, 0x52800190#32, 0x6a12015f#32, 0xb25101ea#32, 0xd36cb012#32, 0x9a8f114a#32, 0x6a20021f#32, 0x53061c10#32, 0x1a9f17e2#32]
def detectChunk4Words : List (BitVec 32) := [0xd3657e52#32, 0x53051c0f#32, 0x0a020102#32, 0x6a0e005f#32, 0x0a11020e#32, 0xb27e0131#32, 0xaa038a50#32, 0x9a891229#32, 0x53134c11#32, 0x0a0101ef#32, 0x0a0e010e#32, 0x6a0d01df#32, 0x0a0c01ec#32, 0xaa11320f#32, 0xb27a0130#32, 0x12001c0d#32, 0x0a08018c#32, 0x9a891209#32, 0x53041c0e#32, 0xd371c410#32, 0x530105ad#32, 0x6a0b019f#32, 0xb27b012b#32, 0x9a891169#32, 0xd35bfc0b#32, 0xd373e80c#32, 0x6a0d01df#32, 0xaa1085ee#32, 0xd370c00d#32, 0x9279016b#32, 0xd34efc0f#32, 0x0a0c020c#32, 0xd36db410#32, 0xaa0b01cb#32, 0xb27c012e#32, 0x9a8e0129#32, 0x2a0d03ed#32, 0x5290000e#32, 0xaa0d656b#32, 0x6a0f021f#32, 0xb27d012d#32, 0x52900010#32, 0x9a8911ad#32, 0x6a0f0189#32, 0x72a00410#32, 0xaa0a016b#32, 0x530e380c#32, 0x9a8e120a#32, 0xd374d00e#32, 0xf24e001f#32, 0xaa0b014f#32, 0x1a8903e9#32]
def detectChunk5Words : List (BitVec 32) := [0x9a8d01aa#32, 0x9a8f016b#32, 0x6a0901cd#32, 0xb268016e#32, 0xb269056f#32, 0xb26a0970#32, 0x9a8b11ce#32, 0x720001bf#32, 0x9a8b11ed#32, 0x9a8b120b#32, 0xf24a001f#32, 0x5317780f#32, 0x9a8b01ab#32, 0xf24b001f#32, 0x9a8b01cb#32, 0xd35e7810#32, 0x6a0f019f#32, 0xb250016d#32, 0x9a8b11ae#32, 0xf268001f#32, 0xb24701ce#32, 0x9a8e01ad#32, 0x6a0f019f#32, 0x9a8b11ae#32, 0xf267001f#32, 0xb24b01ce#32, 0x9a8e01ad#32, 0x6a0f018c#32, 0xd365940e#32, 0x9a8b11ab#32, 0x0a10018d#32, 0xb248016f#32, 0x6a0d011f#32, 0x9a8b11e8#32, 0x6a0e019f#32, 0xb24f010b#32, 0x9a88116d#32, 0xf25a001f#32, 0xb24e01ad#32, 0x9a8d016b#32, 0x6a0e019f#32, 0xd2c4400d#32, 0x9a88116f#32, 0xea2001bf#32, 0xb24d01ed#32, 0x9a8b01ab#32, 0x6a0e019f#32, 0x9a88116d#32, 0xf256001f#32, 0xb24c01ad#32, 0x9a8d016b#32, 0x6a0e018c#32]
def detectChunk6Words : List (BitVec 32) := [0xd379e40e#32, 0x531f7c0d#32, 0x9a881168#32, 0x7200013f#32, 0xaa0ee908#32, 0x2a0d03eb#32, 0x9245000d#32, 0xaa0b214b#32, 0xb249010a#32, 0xb24a050e#32, 0x9a88114a#32, 0x9a8811ce#32, 0xf246001f#32, 0x9a8e014a#32, 0xf10001bf#32, 0xd37cf00d#32, 0x9a8a010a#32, 0x9a8b016e#32, 0x7100059f#32, 0x9a8a110a#32, 0x0a0d0188#32, 0x9a8e1161#32, 0x6a090109#32, 0xb2420148#32, 0x9a8a1108#32, 0xb6e80100#32, 0xb2430548#32, 0x7200013f#32, 0x9a8a1108#32, 0xb6f00080#32, 0xb2440948#32, 0x7200013f#32, 0x9a8a1108#32]
def detectInitHeadInstrs (L : StdBinaryLayout) : List Instr :=
  decodeWords [0xd102c3ff#32, 0xa9077bfd#32, 0xa9085ff8#32, 0xa90957f6#32, 0xa90a4ff4#32, 0x9101c3fd#32, 0x52800200#32] ++ [.bl (L.getauxvalAddr - (L.detectAndInitializeAddr + 0x1c#64))] ++
  decodeWords [0xaa0003f3#32, 0x52800340#32] ++ [.bl (L.getauxvalAddr - (L.detectAndInitializeAddr + 0x28#64))] ++ decodeWords [0xaa130008#32, 0xb40025e8#32]
def detectInitTailInstrs (L : StdBinaryLayout) : List Instr :=
  [decodeWord 0xb2410109#32, .adr true (.gpr 10#5) (adrpOff (L.detectAndInitializeAddr + 0x4c8#64) L.stdDetectCacheAddr), decodeWord 0xaa0803e0#32, .str .X64 (.gpr 9#5) (.Offset (.gpr 10#5) (pageLo12 L.stdDetectCacheAddr))] ++
  decodeWords [0xa94a4ff4#32, 0xa94957f6#32, 0xa9485ff8#32, 0xa9477bfd#32, 0x9102c3ff#32, 0xd65f03c0#32]
/-- Parametric 315-instruction fast path (`+0x000..+0x4e8`) of `detect_and_initialize` at `L.detectAndInitializeAddr`. -/
def detectInitFastInstrs (L : StdBinaryLayout) : List Instr :=
  detectInitHeadInstrs L ++ decodeWords detectChunk1Words ++ decodeWords detectChunk2Words ++ decodeWords detectChunk3Words ++ decodeWords detectChunk4Words ++ decodeWords detectChunk5Words ++ decodeWords detectChunk6Words ++ detectInitTailInstrs L
/-- Parametric 11-instruction list for `RUST_LSE_INIT::init_lse` at `L.initLseAddr`. -/
def initLseInstrs (L : StdBinaryLayout) : List Instr :=
  [.adr true (.gpr 8#5) (adrpOff L.initLseAddr L.stdDetectCacheAddr), .ldr .W64 .X64 false (.gpr 8#5) (.Offset (.gpr 8#5) (pageLo12 L.stdDetectCacheAddr))] ++
  decodeWords [0xb4000068#32, 0x37f000e8#32, 0xd65f03c0#32, 0xa9bf7bfd#32, 0x910003fd#32] ++ [.bl (L.detectAndInitializeAddr - (L.initLseAddr + 0x1c#64))] ++ decodeWords [0xa8c17bfd#32, 0x36f7ff60#32] ++ [.b (L.rustEnableLseAddr - (L.initLseAddr + 0x28#64))]
/-- Parametric 16-instruction list for `libc_start_init` at `L.libcStartInitAddr`. -/
def libcStartInitInstrs (L : StdBinaryLayout) : List Instr :=
  decodeWords [0xa9be7bfd#32, 0x910003fd#32, 0xa90153f3#32] ++ [.adr true (.gpr 19#5) (adrpOff (L.libcStartInitAddr + 0x0c#64) (L.gotAddr + 0x50#64)), .adr true (.gpr 20#5) (adrpOff (L.libcStartInitAddr + 0x10#64) (L.gotAddr + 0x58#64)),
    .bl (L.initFnAddr - (L.libcStartInitAddr + 0x14#64)), .ldr .W64 .X64 false (.gpr 19#5) (.Offset (.gpr 19#5) (pageLo12 (L.gotAddr + 0x50#64))), .ldr .W64 .X64 false (.gpr 20#5) (.Offset (.gpr 20#5) (pageLo12 (L.gotAddr + 0x58#64)))] ++
  decodeWords [0xeb14027f#32, 0x54000082#32, 0xf8408660#32, 0xd63f0000#32, 0x17fffffc#32, 0xa94153f3#32, 0xa8c27bfd#32, 0xd65f03c0#32]
/-- Parametric 14-instruction entry slice (`+0x000..+0x034`) of `libc_start_main_stage2` at `L.libcStartMainStage2Addr`. -/
def libcStartMainStage2EntryInstrs (L : StdBinaryLayout) : List Instr :=
  decodeWords [0xa9bd7bfd#32, 0x910003fd#32, 0xa9025bf5#32, 0x8b21cc56#32, 0xaa0003f5#32, 0x910022d6#32, 0xa90153f3#32, 0x2a0103f3#32, 0xaa0203f4#32] ++
  [.bl (L.libcStartInitAddr - (L.libcStartMainStage2Addr + 0x24#64))] ++ decodeWords [0xaa1603e2#32, 0xaa1403e1#32, 0x2a1303e0#32, 0xd63f02a0#32]
theorem hasInstrs.split_append {P : Program} {base off : BitVec 64} {xs ys : List Instr}
    (h : hasInstrs P base (xs ++ ys)) (hoff : BitVec.ofNat 64 (4 * xs.length) = off := by rfl) : hasInstrs P base xs ∧ hasInstrs P (base + off) ys := by
  refine ⟨fun i hi => by rw [h i (by rw [List.length_append]; omega), List.getElem_append_left hi], fun j hj => ?_⟩
  have hadd : base + off + BitVec.ofNat 64 (4 * j) = base + BitVec.ofNat 64 (4 * (xs.length + j)) := by rw [← hoff, BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.mul_add]
  rw [hadd, h (xs.length + j) (by rw [List.length_append]; omega), List.getElem_append_right (Nat.le_add_right _ _)]; simp
theorem hasInstrs.fetch_at {P : Program} {base off : BitVec 64} {instrs : List Instr} (h : hasInstrs P base instrs) (i : Nat) {inst : Instr}
    (hget : instrs[i]? = some inst := by rfl) (hoff : BitVec.ofNat 64 (4 * i) = off := by rfl) : P.fetch (base + off) = some inst := by
  obtain ⟨hi, hget'⟩ := List.getElem?_eq_some_iff.mp hget; rw [← hoff, h i hi, hget']
theorem hasInstrs.fetch_at_zero {P : Program} {base : BitVec 64} {instrs : List Instr} (h : hasInstrs P base instrs) {inst : Instr}
    (hget : instrs[0]? = some inst := by rfl) : P.fetch base = some inst := by simpa using h.fetch_at 0 (off := 0#64) hget rfl
private meta def foldBitVecLits (e : Lean.Expr) : Lean.MetaM Lean.Expr :=
  Lean.Meta.transform e (pre := fun sub => do
    if sub.isAppOfArity ``BitVec.ofFin 2 && (sub.getArg! 1).isAppOfArity ``Fin.mk 3 then return .done (Lean.mkApp2 (Lean.mkConst ``BitVec.ofNat) (sub.getArg! 0) ((sub.getArg! 1).getArg! 1))
    return .continue)
elab "have_instrs" h:ident startIdx:num count:num : tactic => do
  for k in [0:count.getNat] do
    let i := startIdx.getNat + k; let fnId := Lean.Name.mkSimple s!"hf_{i}"; let fnName := Lean.mkIdent fnId
    let iStx := Lean.Syntax.mkNumLit (toString i); let offStx := Lean.Syntax.mkNumLit (toString (4 * i))
    if i == 0 then Lean.Elab.Tactic.evalTactic (← `(tactic| have $fnName := ProofLib.StdStartup.hasInstrs.fetch_at_zero $h))
    else Lean.Elab.Tactic.evalTactic (← `(tactic| (have $fnName := ProofLib.StdStartup.hasInstrs.fetch_at $h $iStx (off := BitVec.ofNat 64 $offStx); try simp (config := { ground := true }) only [BitVec.add_assoc] at $fnName:ident)))
    Lean.Elab.Tactic.liftMetaTactic1 fun mvarId => mvarId.withContext do
      let some decl := (← Lean.MonadLCtx.getLCtx).findFromUserName? fnId | return mvarId
      let ty ← Lean.instantiateMVars decl.type
      if ty.isAppOfArity ``Eq 3 && ty.appArg!.isAppOfArity ``Option.some 2 && ty.appArg!.appArg!.isAppOfArity ``ProofLib.StdStartup.decodeWord 1 then
        let instClean ← foldBitVecLits (← Lean.Meta.reduce ty.appArg!.appArg! (explicitOnly := false) (skipTypes := true) (skipProofs := true))
        let newTy ← Lean.Meta.mkEq (ty.getArg! 1) (Lean.mkApp2 (Lean.mkConst ``Option.some [0]) (Lean.mkConst ``Instr) instClean)
        let (_, mvarId') ← (← mvarId.assert fnId newTy decl.toExpr).intro1P; return ← mvarId'.tryClear decl.fvarId
      return mvarId
private theorem step_str8_perm {prog : Program} {target_pc pc ea : BitVec 64} {s : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} {val : BitVec 8} (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .B8 rt addr)) (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb)) (hval : (s.readReg32 rt).truncate 8 = val) (hstore : SepStore8 ea val P P')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') P' post oom) : SepWP prog target_pc s P post oom := by
  unfold SepWP; intro R hm; have htrunc : (s.readReg64 rt).truncate 8 = val := bitvec_truncate8_truncate32 _ ▸ hval
  let m' := s.mem.write8 ea val; have hm' := hstore.store hm; have hcan := hstore.writable hm; apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .B8 rt addr) s = ((applyWriteback s wb).setPC (pc + 4#64)).setMem m' := by
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, htrunc, hcan, MemWidth.bytes, hpc, m']
  rw [hstep]; have hn := hnext m' (Memory.perm_write8 s.mem ea val); unfold SepWP at hn; exact hn R hm'
private theorem step_str64_perm {prog : Program} {target_pc pc ea val : BitVec 64} {s : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .X64 rt addr)) (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb)) (hval : s.readReg64 rt = val) (hstore : SepStore64 ea val P P')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') P' post oom) : SepWP prog target_pc s P post oom := by
  unfold SepWP; intro R hm; let m' := s.mem.write64 ea val; have hm' := hstore.store hm; have hcan := hstore.writable hm; apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .X64 rt addr) s = ((applyWriteback s wb).setPC (pc + 4#64)).setMem m' := by
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hval, hcan, MemWidth.bytes, hpc, m']
  rw [hstep]; have hn := hnext m' (Memory.perm_write64 s.mem ea val); unfold SepWP at hn; exact hn R hm'
private theorem step_stp64_perm {prog : Program} {target_pc pc ea ea2 v1 v2 : BitVec 64} {s : State} {P P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt1 rt2 : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stp .W64 rt1 rt2 addr)) (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb)) (hea2 : ea + 8#64 = ea2)
    (hv1 : s.readReg64 rt1 = v1) (hv2 : s.readReg64 rt2 = v2) (hstore1 : SepStore64 ea v1 P P1) (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') P2 post oom) : SepWP prog target_pc s P post oom := by
  unfold SepWP; intro R hm; let m1 := s.mem.write64 ea v1; let m2 := m1.write64 ea2 v2
  have hm1 := hstore1.store hm; have hm2 := hstore2.store hm1; have hcan1 := hstore1.writable hm; have hcan2 := hstore2.writable hm1
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan2; apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.stp .W64 rt1 rt2 addr) s = ((applyWriteback s wb).setPC (pc + 4#64)).setMem m2 := by
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStp, Memory.writeSized, applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hea2, hv1, hv2, hcan1, hcan2, MemWidth.bytes, hpc, m1, m2]
  rw [hstep]; have hn := hnext m2 ((Memory.perm_write64 m1 ea2 v2).trans (Memory.perm_write64 s.mem ea v1)); unfold SepWP at hn; exact hn R hm2
def stdInitFnSpec : Spec Unit where
  pre := fun _ s0 => stackFrameAt s0.sp 0x10; post := fun _ s0 sf => ⌜StdStatePreserved s0 sf⌝ ∗ stackFrameAt s0.sp 0x10
  onPanic := fun _ _ _ => ⌜False⌝; onExit := fun _ _ _ _ => ⌜False⌝; onOom := fun _ _ _ => ⌜False⌝
def stdDoInitSpec (L : StdBinaryLayout) : Spec (BitVec 8) where
  pre := fun initVal _ => (L.initializedAddr ↦₈ initVal) ∗ ((L.gotAddr + 0x30#64) ↦₆₄ 0#64)
  post := fun initVal s0 sf => ⌜StdStatePreserved s0 sf⌝ ∗ ((L.initializedAddr ↦₈ (if initVal == 0#8 then 1#8 else initVal)) ∗ ((L.gotAddr + 0x30#64) ↦₆₄ 0#64))
  onPanic := fun _ _ _ => ⌜False⌝; onExit := fun _ _ _ _ => ⌜False⌝; onOom := fun _ _ _ => ⌜False⌝
/-- Contract for `getauxval(tag)` when `tag != 0x17#64` is present in `entries` with non-zero tags. -/
def stdGetauxvalSpec (L : StdBinaryLayout) : Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 64 × BitVec 64)) where
  pre := fun (tag, val, auxvAddr, entries) s0 => ⌜s0.readReg64 (.gpr 0#5) = tag ∧ tag ≠ 0x17#64 ∧ (∀ t v, (t, v) ∈ entries → t ≠ 0#64) ∧ entries.find? (·.1 == tag) = some (tag, val)⌝ ∗ (((L.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗ (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗ stackFrameAt s0.sp 0x20)
  post := fun (_, val, auxvAddr, entries) s0 sf => ⌜sf.readReg64 (.gpr 0#5) = val ∧ StdStatePreserved s0 sf⌝ ∗ (((L.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗ (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗ stackFrameAt s0.sp 0x20)
  onPanic := fun _ _ _ => ⌜False⌝; onExit := fun _ _ _ _ => ⌜False⌝; onOom := fun _ _ _ => ⌜False⌝
/-- Contract for `detect_and_initialize` under `hwcap &&& 0x3#64 = 0x3#64` (FP + ASIMD). -/
def stdDetectAndInitializeSpec (L : StdBinaryLayout) : Spec (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 64 × BitVec 64)) where
  pre := fun (hwcap, hwcap2, oldCache, auxvAddr, entries) s0 => ⌜hwcap &&& 0x3#64 = 0x3#64 ∧ (∀ t v, (t, v) ∈ entries → t ≠ 0#64) ∧ entries.find? (·.1 == 16#64) = some (16#64, hwcap) ∧ entries.find? (·.1 == 26#64) = some (26#64, hwcap2)⌝ ∗ ((L.stdDetectCacheAddr ↦₆₄ oldCache) ∗ ((L.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗ (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗ stackFrameAt s0.sp 0xd0)
  post := fun (hwcap, _, _, auxvAddr, entries) s0 sf => ⌜(sf.readReg64 (.gpr 0#5)).getLsbD 30 = hwcap.getLsbD 8 ∧ StdStatePreserved s0 sf⌝ ∗ ((∃∗ cacheVal, L.stdDetectCacheAddr ↦₆₄ cacheVal) ∗ ((L.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗ (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗ stackFrameAt s0.sp 0xd0)
  onPanic := fun _ _ _ => ⌜False⌝; onExit := fun _ _ _ _ => ⌜False⌝; onOom := fun _ _ _ => ⌜False⌝
/-- Contract for `RUST_LSE_INIT::init_lse` starting from `haveLseAtomics = 0#8` and `stdDetectCache = 0#64`. -/
def stdInitLseSpec (L : StdBinaryLayout) : Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 64 × BitVec 64)) where
  pre := fun (hwcap, hwcap2, auxvAddr, entries) s0 => ⌜hwcap &&& 0x3#64 = 0x3#64 ∧ (∀ t v, (t, v) ∈ entries → t ≠ 0#64) ∧ entries.find? (·.1 == 16#64) = some (16#64, hwcap) ∧ entries.find? (·.1 == 26#64) = some (26#64, hwcap2)⌝ ∗ ((L.haveLseAtomicsAddr ↦₈ 0#8) ∗ (L.stdDetectCacheAddr ↦₆₄ 0#64) ∗ ((L.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗ (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗ stackFrameAt s0.sp 0xe0)
  post := fun (hwcap, _, auxvAddr, entries) s0 sf => ⌜StdStatePreserved s0 sf⌝ ∗ ((L.haveLseAtomicsAddr ↦₈ (if hwcap.getLsbD 8 then 1#8 else 0#8)) ∗ (∃∗ cacheVal, L.stdDetectCacheAddr ↦₆₄ cacheVal) ∗ ((L.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗ (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗ stackFrameAt s0.sp 0xe0)
  onPanic := fun _ _ _ => ⌜False⌝; onExit := fun _ _ _ _ => ⌜False⌝; onOom := fun _ _ _ => ⌜False⌝
/-- Global footprint before `libc_start_init`. -/
abbrev stdInitGlobalsPre (L : StdBinaryLayout) (auxvAddr : BitVec 64) (entries : List (BitVec 64 × BitVec 64)) : SepProp :=
  (L.initializedAddr ↦₈ 0#8) ∗ (L.haveLseAtomicsAddr ↦₈ 0#8) ∗ (L.stdDetectCacheAddr ↦₆₄ 0#64) ∗ ((L.gotAddr + 0x30#64) ↦₆₄ 0#64) ∗ ((L.gotAddr + 0x50#64) ↦₆₄ L.initArrayAddr) ∗ ((L.gotAddr + 0x58#64) ↦₆₄ (L.initArrayAddr + 0x10#64)) ∗ (L.initArrayAddr ↦₆₄ L.initLseAddr) ∗ ((L.initArrayAddr + 8#64) ↦₆₄ L.doInitAddr) ∗ ((L.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗ (auxvAddr ↦ₛ encodeAuxvBytes entries)
/-- Global footprint after `libc_start_init`. -/
abbrev stdInitGlobalsPost (L : StdBinaryLayout) (hwcap auxvAddr : BitVec 64) (entries : List (BitVec 64 × BitVec 64)) : SepProp :=
  (L.initializedAddr ↦₈ 1#8) ∗ (L.haveLseAtomicsAddr ↦₈ (if hwcap.getLsbD 8 then 1#8 else 0#8)) ∗ (∃∗ cacheVal, L.stdDetectCacheAddr ↦₆₄ cacheVal) ∗ ((L.gotAddr + 0x30#64) ↦₆₄ 0#64) ∗ ((L.gotAddr + 0x50#64) ↦₆₄ L.initArrayAddr) ∗ ((L.gotAddr + 0x58#64) ↦₆₄ (L.initArrayAddr + 0x10#64)) ∗ (L.initArrayAddr ↦₆₄ L.initLseAddr) ∗ ((L.initArrayAddr + 8#64) ↦₆₄ L.doInitAddr) ∗ ((L.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗ (auxvAddr ↦ₛ encodeAuxvBytes entries)
/-- Contract for `libc_start_init` executing `_init`, `RUST_LSE_INIT::init_lse`, and `__do_init`. -/
def stdLibcStartInitSpec (L : StdBinaryLayout) : Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 64 × BitVec 64)) where
  pre := fun (hwcap, hwcap2, auxvAddr, entries) s0 => ⌜hwcap &&& 0x3#64 = 0x3#64 ∧ (∀ t v, (t, v) ∈ entries → t ≠ 0#64) ∧ entries.find? (·.1 == 16#64) = some (16#64, hwcap) ∧ entries.find? (·.1 == 26#64) = some (26#64, hwcap2) ∧ L.initArrayAddr.toNat + 16 < 2 ^ 64⌝ ∗ (stdInitGlobalsPre L auxvAddr entries ∗ stackFrameAt s0.sp 0x100)
  post := fun (hwcap, _, auxvAddr, entries) s0 sf => ⌜StdStatePreserved s0 sf⌝ ∗ (stdInitGlobalsPost L hwcap auxvAddr entries ∗ stackFrameAt s0.sp 0x100)
  onPanic := fun _ _ _ => ⌜False⌝; onExit := fun _ _ _ _ => ⌜False⌝; onOom := fun _ _ _ => ⌜False⌝
private theorem pointsToBytes_encodeAuxvBytes_cons (ptr t v : BitVec 64) (rest : List (BitVec 64 × BitVec 64)) :
    (ptr ↦ₛ encodeAuxvBytes ((t, v) :: rest)) = (ptr ↦₆₄ t) ∗ ((ptr + 8#64) ↦₆₄ v) ∗ ((ptr + 16#64) ↦ₛ encodeAuxvBytes rest) := by
  have heq : encodeAuxvBytes ((t, v) :: rest) = unpack64 t ++ (unpack64 v ++ encodeAuxvBytes rest) := by simp [encodeAuxvBytes_eq_flatMap_bytesLE]; rfl
  rw [heq, pointsToBytes_append, pointsToBytes_append, ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes, unpack64_length, BitVec.add_assoc]; rfl
section
arm64_proof_prelude

theorem initFn_ok (P : Program) (addr : BitVec 64) (hc : P.hasCode addr initFnWords) : subroutine_ok P addr stdInitFnSpec := by
  apply subroutine_ok_of_sepWP_init; intro _ R s0 hpc hrun hpre hsp; dsimp only [stdInitFnSpec] at hpre ⊢; refine ⟨stackFrameAt s0.sp 0x10, hpre, ?_⟩
  have hsf : stackFrameAt s0.sp 0x10 = (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ((s0.sp - 16#64) ↦₆₄ w0) ∗ ((s0.sp - 8#64) ↦₆₄ w1)) := by simp [stackFrameAt, stackFrameSlotsFrom, stackFrameSlotsCont]
  rw [hsf]; apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1; have hf0 : P.fetch addr = some (.stp .W64 (.gpr 29#5) (.gpr 30#5) (.PreIndex .sp (-16#64))) := by wp_fetch
  refine step_stp64_perm (ea2 := s0.sp - 8#64) hpc hrun hf0 (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hsp])
    (show evalAddrMode s0 (.PreIndex .sp (-16#64)) = (s0.sp - 16#64, some (.sp, s0.sp - 16#64)) by simp [evalAddrMode, arm64_norm, bv_lin_norm]) (by bv_lin) rfl rfl (by wp_sep_access) (by wp_sep_access) fun m1 hm1 => ?_
  wp_steps 3; apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]); refine ⟨fun hm => ?_, by simp [wp_norm, arm64_norm, bv_lin_norm], by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun a => congrFun hm1 a⟩, Satisfies.mono (sepConj_mono_left ?_) hm⟩
  exact Entails.sepExists_right (s0.readReg64 (.gpr 29#5)) (Entails.sepExists_right (s0.readReg64 (.gpr 30#5)) (by sep_entail))

theorem doInit_ok (P : Program) (L : StdBinaryLayout) (hc : hasInstrs P L.doInitAddr (doInitInstrs L)) : subroutine_ok P L.doInitAddr (stdDoInitSpec L) := by
  apply subroutine_ok_of_sepWP_init; intro initVal R s0 hpc hrun hpre hsp; dsimp only [stdDoInitSpec] at hpre ⊢; refine ⟨(L.initializedAddr ↦₈ initVal) ∗ ((L.gotAddr + 0x30#64) ↦₆₄ 0#64), hpre, ?_⟩
  have_instrs hc 0 8; have_instrs hc 13 1; wp_step; wp_step; by_cases hzero : initVal == 0#8
  · have hiz : initVal = 0#8 := of_decide_eq_true hzero; subst hiz; wp_steps 3
    refine step_str8_perm (ea := L.initializedAddr) (wb := none) (val := 1#8) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) hf_5 rfl (by simp [evalAddrMode, wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by wp_sep_access) fun m1 hm1 => ?_
    wp_steps 3; apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]); refine ⟨fun hm => ?_, by simp [wp_norm, arm64_norm], by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]⟩
    simp only [beq_self_eq_true, ↓reduceIte]; rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun a => congrFun hm1 a⟩, hm⟩
  · have hne8 : initVal ≠ 0#8 := fun h => hzero (by subst h; rfl)
    have hnz : (initVal.zeroExtend 32 != 0#32) = true := by rw [bne_iff_ne]; intro h; exact hne8 (by simpa using congrArg (BitVec.truncate 8) h)
    have hnz64 : (initVal.zeroExtend 64).truncate 32 ≠ 0#32 := fun h => hne8 (by simpa using congrArg (BitVec.truncate 8) h)
    wp_step; wp_step; apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]); refine ⟨fun hm => ?_, by simp [wp_norm, arm64_norm], by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]⟩
    simp only [hzero, Bool.false_eq_true, ↓reduceIte]; rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨ProcessFieldsPreserved.refl s0, hm⟩
private theorem getauxval_scan_loop (P : Program) (L : StdBinaryLayout) (hc : hasInstrs P L.getauxvalAddr (getauxvalInstrs L))
    {target_pc tag val : BitVec 64} {post : State → SepProp → Prop} {oom : State → SepProp}
    (entries : List (BitVec 64 × BitVec 64)) (hnonull : ∀ t v, (t, v) ∈ entries → t ≠ 0#64) (hfind : entries.find? (·.1 == tag) = some (tag, val)) :
    ∀ (ptr : BitVec 64) (s : State) (F : SepProp), s.pc = L.getauxvalAddr + 0x1c#64 → s.status = .Running → s.readReg64 (.gpr 0#5) = tag → s.readReg64 (.gpr 1#5) = ptr →
      (∀ sf : State, sf.pc = L.getauxvalAddr + 0x54#64 → sf.status = .Running → sf.sp = s.sp → sf.readReg64 (.gpr 19#5) = val →
        CalleeSavedPreserved (s.writeReg64 (.gpr 19#5) val) sf → sf.mem = s.mem → ProcessFieldsPreserved s sf → SepWP P target_pc sf ((ptr ↦ₛ encodeAuxvBytes entries) ∗ F) post oom) →
      SepWP P target_pc s ((ptr ↦ₛ encodeAuxvBytes entries) ∗ F) post oom := by
  induction entries with
  | nil => intro _ _ _ _ _ _ _ _; simp at hfind
  | cons kv rest ih =>
    rcases kv with ⟨t, v⟩; intro ptr s F hpc hrun hx0 hx1 hnext; have ht0 : t ≠ 0#64 := hnonull t v (List.mem_cons_self ..)
    have_instrs hc 7 6; have_instrs hc 16 2; rw [pointsToBytes_encodeAuxvBytes_cons]; wp_steps 3; wp_if hcbz
    · exact absurd hcbz ht0
    · wp_step; wp_if hbeq
      · subst hbeq; simp only [List.find?_cons, beq_self_eq_true, Option.some.injEq, Prod.mk.injEq] at hfind; rcases hfind with ⟨_, rfl⟩; wp_steps 2; rw [← pointsToBytes_encodeAuxvBytes_cons]
        exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (ProcessFieldsPreserved.refl s)
      · simp only [List.find?_cons, beq_eq_false_iff_ne.mpr hbeq] at hfind; wp_steps 2
        have hassoc : (((ptr ↦₆₄ t) ∗ ((ptr + 8#64) ↦₆₄ v) ∗ ((ptr + 16#64) ↦ₛ encodeAuxvBytes rest)) ∗ F) = ((ptr + 16#64) ↦ₛ encodeAuxvBytes rest) ∗ ((ptr ↦₆₄ t) ∗ ((ptr + 8#64) ↦₆₄ v) ∗ F) := by apply Entails.antisymm <;> sep_entail
        rw [hassoc]; refine ih (fun t' v' hm => hnonull t' v' (List.mem_cons_of_mem _ hm)) hfind (ptr + 16#64) _ _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
          (by simp [wp_norm, arm64_norm, hx0]) (by simp [wp_norm, arm64_norm]) fun sf hpc_f hrun_f hsp_f hx19_f hcs_f hmem_f hpf_f => ?_
        rw [← hassoc, ← pointsToBytes_encodeAuxvBytes_cons]
        exact hnext sf hpc_f hrun_f (by simpa [wp_norm, arm64_norm] using hsp_f) hx19_f (CalleeSavedPreserved.trans (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]) hcs_f) (by simpa [wp_norm, arm64_norm] using hmem_f) hpf_f

theorem getauxval_found_ok (P : Program) (L : StdBinaryLayout) (hc : hasInstrs P L.getauxvalAddr (getauxvalInstrs L)) : subroutine_ok P L.getauxvalAddr (stdGetauxvalSpec L) := by
  apply subroutine_ok_of_sepWP_init; rintro ⟨tag, val, auxvAddr, entries⟩ R s0 hpc hrun hpre hsp
  dsimp only [stdGetauxvalSpec] at hpre ⊢; rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨⟨hx0, htag17, hnonull, hfind⟩, hpre⟩
  refine ⟨((L.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗ (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗ stackFrameAt s0.sp 0x20, hpre, ?_⟩
  have hsf : stackFrameAt s0.sp 0x20 = (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ((s0.sp - 32#64) ↦₆₄ w0) ∗ ((s0.sp - 24#64) ↦₆₄ w1) ∗ ((s0.sp - 16#64) ↦₆₄ w2) ∗ ((s0.sp - 8#64) ↦₆₄ w3)) := by simp [stackFrameAt, stackFrameSlotsFrom, stackFrameSlotsCont]
  wp_conv_pre => rw [hsf]; simp only [sepExists_sepConj_right]
  apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1; apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3; have_instrs hc 0 7; have_instrs hc 21 4
  refine step_stp64_perm (ea2 := s0.sp - 24#64) hpc hrun hf_0 (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hsp])
    (show evalAddrMode s0 (.PreIndex .sp (-32#64)) = (s0.sp - 32#64, some (.sp, s0.sp - 32#64)) by simp [evalAddrMode, arm64_norm, bv_lin_norm]) (by bv_lin) rfl rfl (by wp_sep_access) (by wp_sep_access) fun m1 hm1 => ?_
  wp_steps 2; refine step_str64_perm (ea := s0.sp - 16#64) (wb := none) (val := s0.readReg64 (.gpr 19#5)) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) hf_3
    (by simp only [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, wp_norm, arm64_norm] at hsp ⊢; bv_bits) (by simp [evalAddrMode, wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by wp_sep_access) fun m2 hm2 => ?_
  wp_step; wp_if hbeq17
  · exact absurd (by simpa [wp_norm, arm64_norm, hx0] using hbeq17) htag17
  · wp_steps 2; have hcomm : ∀ A B C : SepProp, (A ∗ B ∗ C) = (B ∗ A ∗ C) := fun A B C => by apply Entails.antisymm <;> sep_entail
    rw [hcomm]; refine getauxval_scan_loop P L hc entries hnonull hfind auxvAddr _ _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm, hx0]) (by simp [wp_norm, arm64_norm]) fun sf hpc_f hrun_f hsp_f hx19_f hcs_f hmem_f hpf_f => ?_
    rw [hcomm]; have hsp_sf : sf.spAligned = true := by simp only [State.spAligned] at hsp ⊢; rw [hsp_f]; simp only [wp_norm, arm64_norm] at *; bv_bits
    wp_steps 4; apply SepWP.done (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun_f]); refine ⟨fun hm => ?_, by simp [wp_norm, arm64_norm, bv_lin_norm], ?_⟩
    · rw [sepConj_assoc, satisfies_pure_sepConj]
      have hstd : StdStatePreserved s0 _ := ⟨hpf_f.1, hpf_f.2.1, hpf_f.2.2.1, hpf_f.2.2.2.1, hpf_f.2.2.2.2.1, hpf_f.2.2.2.2.2.1, hpf_f.2.2.2.2.2.2.1, fun a => (hpf_f.2.2.2.2.2.2.2 a).trans ((congrFun hm2 a).trans (congrFun hm1 a))⟩
      refine ⟨⟨by simp [wp_norm, arm64_norm], hstd⟩, Satisfies.mono (sepConj_mono_left ?_) hm⟩; rw [hsf]; refine sepConj_mono_right (sepConj_mono_right ?_)
      exact Entails.sepExists_right (s0.readReg64 (.gpr 29#5)) (Entails.sepExists_right (s0.readReg64 (.gpr 30#5)) (Entails.sepExists_right (s0.readReg64 (.gpr 19#5)) (Entails.sepExists_right w3 (by sep_entail))))
    · rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs_f with ⟨_, g20, g21, g22, g23, g24, g25, g26, g27, g28, _, gv⟩
      simp only [wp_norm, arm64_norm] at g20 g21 g22 g23 g24 g25 g26 g27 g28 gv; rw [CalleeSavedPreserved.iff_regs]; simp [wp_norm, arm64_norm, g20, g21, g22, g23, g24, g25, g26, g27, g28, gv]
private theorem getLsbD_ite {w : Nat} (c : Prop) [Decidable c] (a b : BitVec w) (i : Nat) : (if c then a else b).getLsbD i = if c then a.getLsbD i else b.getLsbD i := by split <;> rfl
private theorem getLsbD_zeroExtend' {n m : Nat} (x : BitVec n) (i : Nat) : (BitVec.zeroExtend m x).getLsbD i = (decide (i < m) && x.getLsbD i) := BitVec.getLsbD_setWidth m x i
private theorem getLsbD_truncate' {n m : Nat} (x : BitVec n) (i : Nat) : (BitVec.truncate m x).getLsbD i = (decide (i < m) && x.getLsbD i) := BitVec.getLsbD_setWidth m x i
private theorem tst_bit8_eq_getLsbD8 (hwcap : BitVec 64) : (if ¬(BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 hwcap) &&& 1099511628032#64) == 0#32) = true then true else false) = hwcap.getLsbD 8 := by
  cases hf : hwcap.getLsbD 8 <;> split <;> rename_i h <;> simp only [beq_iff_eq, Classical.not_not] at h <;> try rfl
  · exact absurd (by bv_bits) h
  · have hb := congrArg (fun x => x.getLsbD 8) h; simp (config := { ground := true }) only [BitVec.getLsbD_setWidth, BitVec.getLsbD_and, BitVec.getLsbD_ofNat, hf] at hb
macro "close_bit_prop" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (simp only [wp_norm, arm64_norm, $hs,*]; simp (config := { decide := true, ground := true }) only [getLsbD_ite, ite_self, getLsbD_zeroExtend', getLsbD_truncate',
    BitVec.getLsbD_ofNat, tst_bit8_eq_getLsbD8, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_or, Bool.or_false, Bool.true_or, Bool.or_true, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, $hs,*]))
private def PureChunkRel (s sf : State) : Prop := sf.sp = s.sp ∧ CalleeSavedPreserved s sf ∧ sf.mem = s.mem ∧ StdStatePreserved s sf
private theorem PureChunkRel.trans {s1 s2 s3 : State} (h1 : PureChunkRel s1 s2) (h2 : PureChunkRel s2 s3) : PureChunkRel s1 s3 := ⟨h2.1.trans h1.1, h1.2.1.trans h2.2.1, h2.2.2.1.trans h1.2.2.1, h1.2.2.2.trans h2.2.2.2⟩
private theorem sig_pc (s : State) (p : BitVec 64) : (s.setPC p).sigActions = s.sigActions := by cases s; rfl
private theorem sig_w64 (s : State) (r : Reg) (v : BitVec 64) : (s.writeReg64 r v).sigActions = s.sigActions := by cases s; cases r <;> rfl
private theorem sig_ps (s : State) (p : PState) : (s.setPState p).sigActions = s.sigActions := by cases s; rfl
private theorem sig_mem (s : State) (m : Memory) : (s.setMem m).sigActions = s.sigActions := by cases s; rfl
macro "close_chunk_rel" s:ident : tactic => `(tactic| refine ⟨by simp [wp_norm, arm64_norm], by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm], by simp [wp_norm, arm64_norm], ProcessFieldsPreserved.refl $s⟩)
private theorem detect_chunk1 (P : Program) (base hwcap : BitVec 64) (hc : hasInstrs P base (decodeWords detectChunk1Words))
    {target_pc : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp} (hpc : s.pc = base) (hrun : s.status = .Running) (hx19 : s.readReg64 (.gpr 19#5) = hwcap)
    (hnext : ∀ sf : State, sf.pc = base + 0xcc#64 → sf.status = .Running → sf.readReg64 (.gpr 19#5) = hwcap → (sf.readReg64 (.gpr 10#5)).getLsbD 30 = hwcap.getLsbD 8 → (sf.readReg64 (.gpr 13#5)).getLsbD 22 = false → (sf.readReg64 (.gpr 11#5)).getLsbD 12 = false → PureChunkRel s sf → SepWP P target_pc sf Pre post oom) : SepWP P target_pc s Pre post oom := by
  have_instrs hc 0 51; wp_steps 51; exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm, hx19]) (by simp only [LogicalOp.ofBits]; close_bit_prop [hx19]) (by close_bit_prop [hx19]) (by close_bit_prop [hx19]) (by close_chunk_rel s)
private theorem detect_chunk2 (P : Program) (base hwcap : BitVec 64) (hc : hasInstrs P base (decodeWords detectChunk2Words))
    {target_pc : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = base) (hrun : s.status = .Running) (hx19 : s.readReg64 (.gpr 19#5) = hwcap) (hx10 : (s.readReg64 (.gpr 10#5)).getLsbD 30 = hwcap.getLsbD 8) (hx13 : (s.readReg64 (.gpr 13#5)).getLsbD 22 = false) (hx11 : (s.readReg64 (.gpr 11#5)).getLsbD 12 = false)
    (hnext : ∀ sf : State, sf.pc = base + 0xd0#64 → sf.status = .Running → sf.readReg64 (.gpr 19#5) = hwcap → (sf.readReg64 (.gpr 8#5)).getLsbD 30 = hwcap.getLsbD 8 → (sf.readReg64 (.gpr 11#5)).getLsbD 30 = hwcap.getLsbD 8 → PureChunkRel s sf → SepWP P target_pc sf Pre post oom) : SepWP P target_pc s Pre post oom := by
  have_instrs hc 0 52; wp_steps 52; exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm, hx19]) (by close_bit_prop [hx19, hx10, hx13, hx11]) (by close_bit_prop [hx19, hx10, hx13, hx11]) (by close_chunk_rel s)
private theorem detect_chunk3 (P : Program) (base hwcap : BitVec 64) (hc : hasInstrs P base (decodeWords detectChunk3Words))
    {target_pc : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = base) (hrun : s.status = .Running) (hx19 : s.readReg64 (.gpr 19#5) = hwcap) (hx8 : (s.readReg64 (.gpr 8#5)).getLsbD 30 = hwcap.getLsbD 8) (hx11 : (s.readReg64 (.gpr 11#5)).getLsbD 30 = hwcap.getLsbD 8)
    (hnext : ∀ sf : State, sf.pc = base + 0xd0#64 → sf.status = .Running → sf.readReg64 (.gpr 19#5) = hwcap → (sf.readReg64 (.gpr 10#5)).getLsbD 30 = hwcap.getLsbD 8 → (sf.readReg64 (.gpr 18#5)).getLsbD 3 = false → PureChunkRel s sf → SepWP P target_pc sf Pre post oom) : SepWP P target_pc s Pre post oom := by
  have_instrs hc 0 52; wp_steps 52; exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm, hx19]) (by close_bit_prop [hx19, hx8, hx11]) (by close_bit_prop [hx19, hx8, hx11]) (by close_chunk_rel s)

private theorem detect_chunk4 (P : Program) (base hwcap : BitVec 64) (hc : hasInstrs P base (decodeWords detectChunk4Words))
    {target_pc : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = base) (hrun : s.status = .Running) (hx19 : s.readReg64 (.gpr 19#5) = hwcap) (hx10 : (s.readReg64 (.gpr 10#5)).getLsbD 30 = hwcap.getLsbD 8) (hx18 : (s.readReg64 (.gpr 18#5)).getLsbD 3 = false)
    (hnext : ∀ sf : State, sf.pc = base + 0xd0#64 → sf.status = .Running → sf.readReg64 (.gpr 19#5) = hwcap → (sf.readReg64 (.gpr 11#5)).getLsbD 30 = hwcap.getLsbD 8 → (sf.readReg64 (.gpr 15#5)).getLsbD 30 = hwcap.getLsbD 8 → PureChunkRel s sf → SepWP P target_pc sf Pre post oom) : SepWP P target_pc s Pre post oom := by
  have_instrs hc 0 52; wp_steps 52; exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm, hx19]) (by close_bit_prop [hx19, hx10, hx18]) (by close_bit_prop [hx19, hx10, hx18]) (by close_chunk_rel s)
private theorem detect_chunk5 (P : Program) (base hwcap : BitVec 64) (hc : hasInstrs P base (decodeWords detectChunk5Words))
    {target_pc : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = base) (hrun : s.status = .Running) (hx11 : (s.readReg64 (.gpr 11#5)).getLsbD 30 = hwcap.getLsbD 8) (hx15 : (s.readReg64 (.gpr 15#5)).getLsbD 30 = hwcap.getLsbD 8)
    (hnext : ∀ sf : State, sf.pc = base + 0xd0#64 → sf.status = .Running → (sf.readReg64 (.gpr 8#5)).getLsbD 30 = hwcap.getLsbD 8 → (sf.readReg64 (.gpr 11#5)).getLsbD 30 = hwcap.getLsbD 8 → PureChunkRel s sf → SepWP P target_pc sf Pre post oom) : SepWP P target_pc s Pre post oom := by
  have_instrs hc 0 52; wp_steps 52; exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) (by close_bit_prop [hx11, hx15]) (by close_bit_prop [hx11, hx15]) (by close_chunk_rel s)
private theorem detect_chunk6 (P : Program) (base hwcap : BitVec 64) (hc : hasInstrs P base (decodeWords detectChunk6Words))
    {target_pc : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = base) (hrun : s.status = .Running) (hx8 : (s.readReg64 (.gpr 8#5)).getLsbD 30 = hwcap.getLsbD 8) (hx11 : (s.readReg64 (.gpr 11#5)).getLsbD 30 = hwcap.getLsbD 8)
    (hnext : ∀ sf : State, sf.pc = base + 0x84#64 → sf.status = .Running → (sf.readReg64 (.gpr 8#5)).getLsbD 30 = hwcap.getLsbD 8 → PureChunkRel s sf → SepWP P target_pc sf Pre post oom) : SepWP P target_pc s Pre post oom := by
  have_instrs hc 0 33; wp_steps 26; wp_if htbz1
  · exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) (by close_bit_prop [hx8, hx11]) (by close_chunk_rel s)
  · wp_steps 4; wp_if htbz2
    · exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) (by close_bit_prop [hx8, hx11]) (by close_chunk_rel s)
    · wp_steps 3; exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) (by close_bit_prop [hx8, hx11]) (by close_chunk_rel s)
private theorem SepWP.let_sp {P : Program} {t sp' : BitVec 64} {s : State} {Pre : SepProp} {post oom} (hsp : s.sp = sp') (h : (s.sp = sp') → SepWP P t s Pre post oom) : SepWP P t s Pre post oom := h hsp
private theorem detectInitFastInstrs_parts {P : Program} {L : StdBinaryLayout} (hc : hasInstrs P L.detectAndInitializeAddr (detectInitFastInstrs L)) :
    hasInstrs P L.detectAndInitializeAddr (detectInitHeadInstrs L) ∧ hasInstrs P (L.detectAndInitializeAddr + 0x34#64) (decodeWords detectChunk1Words) ∧ hasInstrs P (L.detectAndInitializeAddr + 0x100#64) (decodeWords detectChunk2Words) ∧
    hasInstrs P (L.detectAndInitializeAddr + 0x1d0#64) (decodeWords detectChunk3Words) ∧ hasInstrs P (L.detectAndInitializeAddr + 0x2a0#64) (decodeWords detectChunk4Words) ∧ hasInstrs P (L.detectAndInitializeAddr + 0x370#64) (decodeWords detectChunk5Words) ∧
    hasInstrs P (L.detectAndInitializeAddr + 0x440#64) (decodeWords detectChunk6Words) ∧ hasInstrs P (L.detectAndInitializeAddr + 0x4c4#64) (detectInitTailInstrs L) := by
  have ⟨hc, h7⟩ := hc.split_append (off := 0x4c4#64) (by simp only [List.length_append, decodeWords, List.length_map, detectInitHeadInstrs, detectChunk1Words, detectChunk2Words, detectChunk3Words, detectChunk4Words, detectChunk5Words, detectChunk6Words, List.length_cons, List.length_nil])
  have ⟨hc, h6⟩ := hc.split_append (off := 0x440#64) (by simp only [List.length_append, decodeWords, List.length_map, detectInitHeadInstrs, detectChunk1Words, detectChunk2Words, detectChunk3Words, detectChunk4Words, detectChunk5Words, List.length_cons, List.length_nil])
  have ⟨hc, h5⟩ := hc.split_append (off := 0x370#64) (by simp only [List.length_append, decodeWords, List.length_map, detectInitHeadInstrs, detectChunk1Words, detectChunk2Words, detectChunk3Words, detectChunk4Words, List.length_cons, List.length_nil])
  have ⟨hc, h4⟩ := hc.split_append (off := 0x2a0#64) (by simp only [List.length_append, decodeWords, List.length_map, detectInitHeadInstrs, detectChunk1Words, detectChunk2Words, detectChunk3Words, List.length_cons, List.length_nil])
  have ⟨hc, h3⟩ := hc.split_append (off := 0x1d0#64) (by simp only [List.length_append, decodeWords, List.length_map, detectInitHeadInstrs, detectChunk1Words, detectChunk2Words, List.length_cons, List.length_nil]); have ⟨hc, h2⟩ := hc.split_append (off := 0x100#64) (by simp only [List.length_append, decodeWords, List.length_map, detectInitHeadInstrs, detectChunk1Words, List.length_cons, List.length_nil])
  have ⟨h0, h1⟩ := hc.split_append (off := 0x34#64) (by simp only [List.length_append, decodeWords, List.length_map, detectInitHeadInstrs, List.length_cons, List.length_nil]); exact ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩

theorem detectAndInitialize_ok (P : Program) (L : StdBinaryLayout) (hc : hasInstrs P L.detectAndInitializeAddr (detectInitFastInstrs L))
    (hGetauxval : subroutine_ok P L.getauxvalAddr (stdGetauxvalSpec L)) : subroutine_ok P L.detectAndInitializeAddr (stdDetectAndInitializeSpec L) := by
  apply subroutine_ok_of_sepWP_init; rintro ⟨hwcap, hwcap2, oldCache, auxvAddr, entries⟩ R s0 hpc hrun hpre hsp
  dsimp only [stdDetectAndInitializeSpec] at hpre ⊢; rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨⟨hhwcap, hnonull, hfind16, hfind26⟩, hpre⟩
  refine ⟨(L.stdDetectCacheAddr ↦₆₄ oldCache) ∗ ((L.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗ (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗ stackFrameAt s0.sp 0xd0, hpre, ?_⟩
  rcases detectInitFastInstrs_parts hc with ⟨hc_head, hc_1, hc_2, hc_3, hc_4, hc_5, hc_6, hc_tail⟩; clear hc
  have hsf40 : stackFrameAt s0.sp 0x40 = (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
      ((s0.sp - 64#64) ↦₆₄ w0) ∗ ((s0.sp - 56#64) ↦₆₄ w1) ∗ ((s0.sp - 48#64) ↦₆₄ w2) ∗ ((s0.sp - 40#64) ↦₆₄ w3) ∗ ((s0.sp - 32#64) ↦₆₄ w4) ∗ ((s0.sp - 24#64) ↦₆₄ w5) ∗ ((s0.sp - 16#64) ↦₆₄ w6) ∗ ((s0.sp - 8#64) ↦₆₄ w7)) := by simp [stackFrameAt, stackFrameSlotsFrom, stackFrameSlotsCont]
  wp_conv_pre => rw [stackFrameAt_split s0.sp 0xb0 0x20, stackFrameAt_split s0.sp 0x40 0x70, hsf40]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1; apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
  apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5; apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro w7; have_instrs hc_head 0 13; clear hc_head; have hsp0 := sp_and_15_of_spAligned hsp; wp_step
  refine step_stp64_perm (ea := s0.sp - 64#64) (ea2 := s0.sp - 56#64) (v1 := s0.readReg64 (.gpr 29#5)) (v2 := s0.readReg64 (.gpr 30#5)) (wb := none) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) hf_1
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, wp_norm, arm64_norm, hsp0]) (by simp [evalAddrMode, wp_norm, arm64_norm, bv_lin_norm]) (by bv_lin) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by wp_sep_access) (by wp_sep_access) fun m1 hm1 => ?_
  refine step_stp64_perm (ea := s0.sp - 48#64) (ea2 := s0.sp - 40#64) (v1 := s0.readReg64 (.gpr 24#5)) (v2 := s0.readReg64 (.gpr 23#5)) (wb := none) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) hf_2
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, wp_norm, arm64_norm, hsp0]) (by simp [evalAddrMode, wp_norm, arm64_norm, bv_lin_norm]) (by bv_lin) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by wp_sep_access) (by wp_sep_access) fun m2 hm2 => ?_
  refine step_stp64_perm (ea := s0.sp - 32#64) (ea2 := s0.sp - 24#64) (v1 := s0.readReg64 (.gpr 22#5)) (v2 := s0.readReg64 (.gpr 21#5)) (wb := none) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) hf_3
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, wp_norm, arm64_norm, hsp0]) (by simp [evalAddrMode, wp_norm, arm64_norm, bv_lin_norm]) (by bv_lin) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by wp_sep_access) (by wp_sep_access) fun m3 hm3 => ?_
  refine step_stp64_perm (ea := s0.sp - 16#64) (ea2 := s0.sp - 8#64) (v1 := s0.readReg64 (.gpr 20#5)) (v2 := s0.readReg64 (.gpr 19#5)) (wb := none) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) hf_4
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, wp_norm, arm64_norm, hsp0]) (by simp [evalAddrMode, wp_norm, arm64_norm, bv_lin_norm]) (by bv_lin) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by wp_sep_access) (by wp_sep_access) fun m4 hm4 => ?_
  wp_steps 3; refine SepWP.let_sp (sp' := s0.sp - 176#64) (by simp [wp_norm, arm64_norm]) fun hsp_bl1 => ?_
  refine SepWP.call_subroutine_frame_auto hGetauxval (x := (16#64, hwcap, auxvAddr, entries)) (ret_pc := L.detectAndInitializeAddr + 0x20#64) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (by simp [State.spAligned, wp_norm, arm64_norm, hsp0]) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h) (fun sf1 hpc1 hrun1 hsp1 hcs1 => ?_)
    (by dsimp only [stdGetauxvalSpec]; rw [hsp_bl1]; sep_frame (disch := first | assumption | decide | simp [wp_norm, arm64_norm]))
  dsimp only [stdGetauxvalSpec]; wp_conv_pre => rw [hsp_bl1, sepConj_assoc]
  apply SepWP.pure_elim; rintro ⟨hx0_1, hstd1⟩; have hsp1' : sf1.sp = s0.sp - 176#64 := hsp1.trans hsp_bl1; wp_steps 3; refine SepWP.let_sp (sp' := s0.sp - 176#64) (by simp [wp_norm, arm64_norm, hsp1']) fun hsp_bl2 => ?_
  refine SepWP.call_subroutine_frame_auto hGetauxval (x := (26#64, hwcap2, auxvAddr, entries)) (ret_pc := L.detectAndInitializeAddr + 0x2c#64) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun1])
    (by simp [State.spAligned, wp_norm, arm64_norm, hsp1', hsp0]) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h) (fun sf2 hpc2 hrun2 hsp2 hcs2 => ?_)
    (by dsimp only [stdGetauxvalSpec]; rw [hsp_bl2]; sep_frame (disch := first | assumption | decide | simp [wp_norm, arm64_norm]))
  dsimp only [stdGetauxvalSpec]; wp_conv_pre => rw [hsp_bl2, sepConj_assoc]
  apply SepWP.pure_elim; rintro ⟨hx0_2, hstd2⟩; have hsp2' : sf2.sp = s0.sp - 176#64 := hsp2.trans hsp_bl2
  have hx19_2 : sf2.readReg64 (.gpr 19#5) = hwcap := by simpa [wp_norm, arm64_norm, hx0_1] using ((CalleeSavedPreserved.iff_regs _ _).mp hcs2).1
  wp_steps 2; wp_if hcbz
  · exact absurd (by simpa [wp_norm, arm64_norm, hx0_2, hx19_2] using hcbz) (by intro hz; revert hhwcap hz; bv_bits)
  · clear hf_0 hf_1 hf_2 hf_3 hf_4 hf_5 hf_6 hf_7 hf_8 hf_9 hf_10 hf_11 hf_12
    refine detect_chunk1 P _ hwcap hc_1 (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun2]) (by simp [wp_norm, arm64_norm, hx19_2]) fun sc1 hpc_c1 hrun_c1 hx19_c1 hx10_c1 hx13_c1 hx11_c1 hrel1 => ?_
    refine detect_chunk2 P _ hwcap hc_2 (by simpa [bv_lin_norm] using hpc_c1) hrun_c1 hx19_c1 hx10_c1 hx13_c1 hx11_c1 fun sc2 hpc_c2 hrun_c2 hx19_c2 hx8_c2 hx11_c2 hrel2 => ?_
    refine detect_chunk3 P _ hwcap hc_3 (by simpa [bv_lin_norm] using hpc_c2) hrun_c2 hx19_c2 hx8_c2 hx11_c2 fun sc3 hpc_c3 hrun_c3 hx19_c3 hx10_c3 hx18_c3 hrel3 => ?_
    refine detect_chunk4 P _ hwcap hc_4 (by simpa [bv_lin_norm] using hpc_c3) hrun_c3 hx19_c3 hx10_c3 hx18_c3 fun sc4 hpc_c4 hrun_c4 _ hx11_c4 hx15_c4 hrel4 => ?_
    refine detect_chunk5 P _ hwcap hc_5 (by simpa [bv_lin_norm] using hpc_c4) hrun_c4 hx11_c4 hx15_c4 fun sc5 hpc_c5 hrun_c5 hx8_c5 hx11_c5 hrel5 => ?_
    refine detect_chunk6 P _ hwcap hc_6 (by simpa [bv_lin_norm] using hpc_c5) hrun_c5 hx8_c5 hx11_c5 fun sc6 hpc_c6 hrun_c6 hx8_c6 hrel6 => ?_
    clear hc_1 hc_2 hc_3 hc_4 hc_5 hc_6; have hrel := hrel1.trans (hrel2.trans (hrel3.trans (hrel4.trans (hrel5.trans hrel6))))
    replace hpc_c6 : sc6.pc = L.detectAndInitializeAddr + 0x4c4#64 := by simpa [bv_lin_norm] using hpc_c6
    have hsp_c6 : sc6.sp = s0.sp - 176#64 := by simpa [wp_norm, arm64_norm, hsp2'] using hrel.1
    have_instrs hc_tail 0 10; clear hc_tail; wp_steps 3
    refine step_str64_perm (ea := L.stdDetectCacheAddr) (wb := none) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun_c6]) hf_3 rfl (by simp [evalAddrMode, wp_norm, arm64_norm]) rfl (by wp_sep_access) fun m5 hm5 => ?_
    refine SepWP.step_ldp64 (ea := s0.sp - 16#64) (ea2 := s0.sp - 8#64) (wb := none) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun_c6]) hf_4
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, wp_norm, arm64_norm, hsp_c6, hsp0]) (by simp [evalAddrMode, wp_norm, arm64_norm, hsp_c6, bv_lin_norm]) (by bv_lin) (by wp_sep_access) (by wp_sep_access) (by wp_norm_lhs) ?_
    refine SepWP.step_ldp64 (ea := s0.sp - 32#64) (ea2 := s0.sp - 24#64) (wb := none) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun_c6]) hf_5
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, wp_norm, arm64_norm, hsp_c6, hsp0]) (by simp [evalAddrMode, wp_norm, arm64_norm, hsp_c6, bv_lin_norm]) (by bv_lin) (by wp_sep_access) (by wp_sep_access) (by wp_norm_lhs) ?_
    refine SepWP.step_ldp64 (ea := s0.sp - 48#64) (ea2 := s0.sp - 40#64) (wb := none) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun_c6]) hf_6
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, wp_norm, arm64_norm, hsp_c6, hsp0]) (by simp [evalAddrMode, wp_norm, arm64_norm, hsp_c6, bv_lin_norm]) (by bv_lin) (by wp_sep_access) (by wp_sep_access) (by wp_norm_lhs) ?_
    refine SepWP.step_ldp64 (ea := s0.sp - 64#64) (ea2 := s0.sp - 56#64) (wb := none) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun_c6]) hf_7
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, wp_norm, arm64_norm, hsp_c6, hsp0]) (by simp [evalAddrMode, wp_norm, arm64_norm, hsp_c6, bv_lin_norm]) (by bv_lin) (by wp_sep_access) (by wp_sep_access) (by wp_norm_lhs) ?_
    wp_steps 2; apply SepWP.done (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun_c6]); refine ⟨fun hm => ?_, by simp [wp_norm, arm64_norm, bv_lin_norm], ?_⟩
    · rw [sepConj_assoc, satisfies_pure_sepConj]
      rcases hstd1 with ⟨f1, t1, tp1, sa1, bk1, bs1, pm1, p1⟩; simp only [sig_pc, sig_w64, sig_mem, wp_norm, arm64_norm, hm4, hm3, hm2, hm1] at f1 t1 tp1 sa1 bk1 bs1 pm1 p1
      rcases hstd2 with ⟨f2, t2, tp2, sa2, bk2, bs2, pm2, p2⟩; simp only [sig_pc, sig_w64, wp_norm, arm64_norm, f1, t1, tp1, sa1, bk1, bs1, pm1, p1] at f2 t2 tp2 sa2 bk2 bs2 pm2 p2
      rcases hrel.2.2.2 with ⟨f3, t3, tp3, sa3, bk3, bs3, pm3, p3⟩; simp only [sig_pc, sig_w64, wp_norm, arm64_norm, f2, t2, tp2, sa2, bk2, bs2, pm2, p2] at f3 t3 tp3 sa3 bk3 bs3 pm3 p3
      refine ⟨⟨by simpa [wp_norm, arm64_norm] using hx8_c6, ⟨by simp [wp_norm, arm64_norm, f3], by simp [wp_norm, arm64_norm, t3], by simp [wp_norm, arm64_norm, tp3], by simp [sig_mem, sig_pc, sig_w64, sa3], by simp [wp_norm, arm64_norm, bk3], by simp [wp_norm, arm64_norm, bs3], by simp [wp_norm, arm64_norm, pm3], fun a => by simp [wp_norm, arm64_norm, hm5, p3]⟩⟩, ?_⟩
      rw [stackFrameAt_split s0.sp 0xb0 0x20, stackFrameAt_split s0.sp 0x40 0x70, hsf40]; sep_frame
    · rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs1 with ⟨_, _, _, _, _, _, a25, a26, a27, a28, _, av⟩; rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs2 with ⟨_, _, _, _, _, _, b25, b26, b27, b28, _, bv⟩
      rcases (CalleeSavedPreserved.iff_regs _ _).mp hrel.2.1 with ⟨_, _, _, _, _, _, c25, c26, c27, c28, _, cv⟩
      simp only [wp_norm, arm64_norm] at a25 a26 a27 a28 av b25 b26 b27 b28 bv c25 c26 c27 c28 cv; rw [CalleeSavedPreserved.iff_regs]
      simp [wp_norm, arm64_norm, c25, c26, c27, c28, cv, b25, b26, b27, b28, bv, a25, a26, a27, a28, av]

theorem initLse_ok (P : Program) (L : StdBinaryLayout) (hc : hasInstrs P L.initLseAddr (initLseInstrs L))
    (hDetect : subroutine_ok P L.detectAndInitializeAddr (stdDetectAndInitializeSpec L))
    (hEnableLse : subroutine_ok P L.rustEnableLseAddr (stdRustEnableLseSpec L.haveLseAtomicsAddr)) : subroutine_ok P L.initLseAddr (stdInitLseSpec L) := by
  apply subroutine_ok_of_sepWP_init; rintro ⟨hwcap, hwcap2, auxvAddr, entries⟩ R s0 hpc hrun hpre hsp
  dsimp only [stdInitLseSpec] at hpre ⊢; rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨⟨hhwcap, hnonull, hfind16, hfind26⟩, hpre⟩
  refine ⟨(L.haveLseAtomicsAddr ↦₈ 0#8) ∗ (L.stdDetectCacheAddr ↦₆₄ 0#64) ∗ ((L.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗ (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗ stackFrameAt s0.sp 0xe0, hpre, ?_⟩
  have hsf10 : stackFrameAt s0.sp 0x10 = (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ((s0.sp - 16#64) ↦₆₄ w0) ∗ ((s0.sp - 8#64) ↦₆₄ w1)) := by simp [stackFrameAt, stackFrameSlotsFrom, stackFrameSlotsCont]
  wp_conv_pre => rw [stackFrameAt_split s0.sp 0x10 0xd0, hsf10]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1; have_instrs hc 0 11; clear hc; have hsp0 := sp_and_15_of_spAligned hsp; wp_steps 3
  refine step_stp64_perm (ea := s0.sp - 16#64) (ea2 := s0.sp - 8#64) (v1 := s0.readReg64 (.gpr 29#5)) (v2 := s0.readReg64 (.gpr 30#5)) (wb := some (.sp, s0.sp - 16#64))
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) hf_5 (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, wp_norm, arm64_norm, hsp0])
    (by simp [evalAddrMode, wp_norm, arm64_norm, bv_lin_norm]) (by bv_lin) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by wp_sep_access) (by wp_sep_access) fun m1 hm1 => ?_
  wp_steps 2; refine SepWP.let_sp (sp' := s0.sp - 16#64) (by simp [wp_norm, arm64_norm]) fun hsp_bl => ?_
  refine SepWP.call_subroutine_frame_auto hDetect (x := (hwcap, hwcap2, 0#64, auxvAddr, entries)) (ret_pc := L.initLseAddr + 0x20#64) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (by simp [State.spAligned, wp_norm, arm64_norm, hsp0]) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 => ?_) (by dsimp only [stdDetectAndInitializeSpec]; rw [hsp_bl]; sep_frame (disch := assumption))
  dsimp only [stdDetectAndInitializeSpec]; wp_conv_pre => rw [hsp_bl, sepConj_assoc]
  apply SepWP.pure_elim; rintro ⟨hx0_1, hstd1⟩; wp_conv_pre => simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro cacheVal; have hsp1' : sf1.sp = s0.sp - 16#64 := hsp1.trans hsp_bl; have hsp1r : sf1.readReg64 .sp = s0.sp - 16#64 := hsp1'
  refine SepWP.step_ldp64 (ea := s0.sp - 16#64) (ea2 := s0.sp - 8#64) (wb := some (.sp, s0.sp)) hpc1 hrun1 hf_8
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp1', hsp0]) (by simp [evalAddrMode, hsp1r, bv_lin_norm]) (by bv_lin) (by wp_sep_access) (by wp_sep_access) (by wp_norm_lhs) ?_
  rcases hstd1 with ⟨f1, t1, tp1, sa1, bk1, bs1, pm1, p1⟩; simp only [sig_pc, sig_w64, sig_mem, wp_norm, arm64_norm, hm1] at f1 t1 tp1 sa1 bk1 bs1 pm1 p1
  rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs1 with ⟨g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, _, gv⟩
  simp only [wp_norm, arm64_norm] at g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 gv; wp_step; wp_if htbz
  · have hbit : hwcap.getLsbD 8 = false := by simpa [wp_norm, arm64_norm, hx0_1] using htbz
    wp_step; apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1]); refine ⟨fun hm => ?_, by simp [wp_norm, arm64_norm], ?_⟩
    · simp only [hbit, Bool.false_eq_true, ↓reduceIte]; rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨by simp [wp_norm, arm64_norm, f1], by simp [wp_norm, arm64_norm, t1], by simp [wp_norm, arm64_norm, tp1], by simp [sig_pc, sig_w64, sa1], by simp [wp_norm, arm64_norm, bk1], by simp [wp_norm, arm64_norm, bs1], by simp [wp_norm, arm64_norm, pm1], fun a => by simp [wp_norm, arm64_norm, p1]⟩, ?_⟩
      rw [stackFrameAt_split s0.sp 0x10 0xd0, hsf10]; sep_frame
    · rw [CalleeSavedPreserved.iff_regs]; simp [wp_norm, arm64_norm, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, gv]
  · have hbit : hwcap.getLsbD 8 = true := by simpa [wp_norm, arm64_norm, hx0_1] using htbz
    wp_step; refine SepWP.call_subroutine_frame_auto hEnableLse (x := 0#8) (ret_pc := s0.readReg64 (.gpr 30#5)) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      (by simp [State.spAligned, wp_norm, arm64_norm, hsp0]) (by simp [wp_norm, arm64_norm]) (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h) (fun sf2 hpc2 hrun2 hsp2 hcs2 => ?_) (by dsimp only [stdRustEnableLseSpec]; sep_frame)
    dsimp only [stdRustEnableLseSpec]; wp_conv_pre => rw [sepConj_assoc]
    apply SepWP.pure_elim; intro hstd2; apply SepWP.done hpc2 hrun2; refine ⟨fun hm => ?_, by simpa [wp_norm, arm64_norm] using hsp2, ?_⟩
    · simp only [hbit, ↓reduceIte]; rw [sepConj_assoc, satisfies_pure_sepConj]; rcases hstd2 with ⟨f2, t2, tp2, sa2, bk2, bs2, pm2, p2⟩
      simp only [sig_pc, sig_w64, wp_norm, arm64_norm, f1, t1, tp1, sa1, bk1, bs1, pm1, p1] at f2 t2 tp2 sa2 bk2 bs2 pm2 p2
      refine ⟨⟨f2, t2, tp2, sa2, bk2, bs2, pm2, p2⟩, ?_⟩; rw [stackFrameAt_split s0.sp 0x10 0xd0, hsf10]; sep_frame
    · refine CalleeSavedPreserved.trans ?_ hcs2; rw [CalleeSavedPreserved.iff_regs]; simp [wp_norm, arm64_norm, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, gv]

theorem libcStartInit_ok (P : Program) (L : StdBinaryLayout) (hc : hasInstrs P L.libcStartInitAddr (libcStartInitInstrs L))
    (hInitFn : subroutine_ok P L.initFnAddr stdInitFnSpec) (hInitLse : subroutine_ok P L.initLseAddr (stdInitLseSpec L))
    (hDoInit : subroutine_ok P L.doInitAddr (stdDoInitSpec L)) : subroutine_ok P L.libcStartInitAddr (stdLibcStartInitSpec L) := by
  apply subroutine_ok_of_sepWP_init; rintro ⟨hwcap, hwcap2, auxvAddr, entries⟩ R s0 hpc hrun hpre hsp
  dsimp only [stdLibcStartInitSpec, stdInitGlobalsPre, stdInitGlobalsPost] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨⟨hhwcap, hnonull, hfind16, hfind26, hbound⟩, hpre⟩
  refine ⟨stdInitGlobalsPre L auxvAddr entries ∗ stackFrameAt s0.sp 0x100, hpre, ?_⟩; dsimp only [stdInitGlobalsPre]
  have hsf20 : stackFrameAt s0.sp 0x20 = (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ((s0.sp - 32#64) ↦₆₄ w0) ∗ ((s0.sp - 24#64) ↦₆₄ w1) ∗ ((s0.sp - 16#64) ↦₆₄ w2) ∗ ((s0.sp - 8#64) ↦₆₄ w3)) := by simp [stackFrameAt, stackFrameSlotsFrom, stackFrameSlotsCont]
  wp_conv_pre => rw [stackFrameAt_split s0.sp 0x20 0xe0, stackFrameAt_split (s0.sp - 32#64) 0x10 0xd0, hsf20]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1; apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3; have_instrs hc 0 16; clear hc; have hsp0 := sp_and_15_of_spAligned hsp
  refine step_stp64_perm (ea := s0.sp - 32#64) (ea2 := s0.sp - 24#64) (v1 := s0.readReg64 (.gpr 29#5)) (v2 := s0.readReg64 (.gpr 30#5)) (wb := some (.sp, s0.sp - 32#64)) hpc hrun hf_0
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hsp]) (show evalAddrMode s0 (.PreIndex .sp (-32#64)) = (s0.sp - 32#64, some (.sp, s0.sp - 32#64)) by simp [evalAddrMode, arm64_norm, bv_lin_norm])
    (by bv_lin) rfl rfl (by wp_sep_access) (by wp_sep_access) fun m1 hm1 => ?_
  wp_step; refine step_stp64_perm (ea := s0.sp - 16#64) (ea2 := s0.sp - 8#64) (v1 := s0.readReg64 (.gpr 19#5)) (v2 := s0.readReg64 (.gpr 20#5)) (wb := none) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) hf_2
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, wp_norm, arm64_norm, hsp0]) (by simp [evalAddrMode, wp_norm, arm64_norm, bv_lin_norm]) (by bv_lin) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by wp_sep_access) (by wp_sep_access) fun m2 hm2 => ?_
  wp_steps 3; refine SepWP.let_sp (sp' := s0.sp - 32#64) (by simp [wp_norm, arm64_norm]) fun hsp_bl1 => ?_
  refine SepWP.call_subroutine_frame_auto hInitFn (x := ()) (ret_pc := L.libcStartInitAddr + 0x18#64) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (by simp [State.spAligned, wp_norm, arm64_norm, hsp0]) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h) (fun sf1 hpc1 hrun1 hsp1 hcs1 => ?_) (by dsimp only [stdInitFnSpec]; rw [hsp_bl1]; sep_frame)
  dsimp only [stdInitFnSpec]; wp_conv_pre => rw [hsp_bl1, sepConj_assoc]
  apply SepWP.pure_elim; intro hstd1; have hsp1' : sf1.sp = s0.sp - 32#64 := hsp1.trans hsp_bl1
  rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs1 with ⟨hx19_1, hx20_1, a21, a22, a23, a24, a25, a26, a27, a28, _, av⟩; simp only [wp_norm, arm64_norm] at hx19_1 hx20_1 a21 a22 a23 a24 a25 a26 a27 a28 av
  refine SepWP.step_ldr64 (ea := L.gotAddr + 0x50#64) (wb := none) hpc1 hrun1 hf_6 rfl (by simp [evalAddrMode, hx19_1]) (by wp_sep_access) (by wp_norm_lhs) ?_
  refine SepWP.step_ldr64 (ea := L.gotAddr + 0x58#64) (wb := none) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun1]) hf_7 rfl (by simp [evalAddrMode, wp_norm, arm64_norm, hx20_1]) (by wp_sep_access) (by wp_norm_lhs) ?_
  wp_steps 2; wp_if hbhs1
  · have hbad : BitVec.ule (L.initArrayAddr + 16#64) L.initArrayAddr = true := by simpa [wp_norm, arm64_norm] using hbhs1
    simp only [BitVec.ule, decide_eq_true_eq, BitVec.toNat_add, BitVec.toNat_ofNat] at hbad; omega
  · refine SepWP.step_ldr64 (ea := L.initArrayAddr) (wb := some (.gpr 19#5, L.initArrayAddr + 8#64)) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun1]) hf_10 rfl (by simp [evalAddrMode, wp_norm, arm64_norm]) (by wp_sep_access) (by wp_norm_lhs) ?_
    wp_step; refine SepWP.let_sp (sp' := s0.sp - 32#64) (by simp [wp_norm, arm64_norm, hsp1']) fun hsp_bl2 => ?_
    refine SepWP.call_subroutine_frame_auto hInitLse (x := (hwcap, hwcap2, auxvAddr, entries)) (ret_pc := L.libcStartInitAddr + 0x30#64) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      (by simp [State.spAligned, wp_norm, arm64_norm, hsp1', hsp0]) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h)
      (fun sf2 hpc2 hrun2 hsp2 hcs2 => ?_) (by dsimp only [stdInitLseSpec]; rw [hsp_bl2, stackFrameAt_split (s0.sp - 32#64) 0x10 0xd0]; sep_frame (disch := assumption))
    dsimp only [stdInitLseSpec]; wp_conv_pre => rw [hsp_bl2, sepConj_assoc]
    apply SepWP.pure_elim; intro hstd2; wp_conv_pre => simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro cacheVal; have hsp2' : sf2.sp = s0.sp - 32#64 := hsp2.trans hsp_bl2
    rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs2 with ⟨hx19_2, hx20_2, b21, b22, b23, b24, b25, b26, b27, b28, _, bv⟩
    simp only [wp_norm, arm64_norm, a21, a22, a23, a24, a25, a26, a27, a28, av] at hx19_2 hx20_2 b21 b22 b23 b24 b25 b26 b27 b28 bv; wp_steps 3; wp_if hbhs2
    · have hbad : BitVec.ule (L.initArrayAddr + 16#64) (L.initArrayAddr + 8#64) = true := by simpa [wp_norm, arm64_norm, hx19_2, hx20_2] using hbhs2
      simp only [BitVec.ule, decide_eq_true_eq, BitVec.toNat_add, BitVec.toNat_ofNat] at hbad; omega
    · refine SepWP.step_ldr64 (ea := L.initArrayAddr + 8#64) (wb := some (.gpr 19#5, L.initArrayAddr + 16#64)) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun2]) hf_10 rfl (by simp [evalAddrMode, wp_norm, arm64_norm, hx19_2, bv_lin_norm]) (by wp_sep_access) (by wp_norm_lhs) ?_
      wp_step; refine SepWP.call_subroutine_frame_auto hDoInit (x := 0#8) (ret_pc := L.libcStartInitAddr + 0x30#64) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun2])
        (by simp [State.spAligned, wp_norm, arm64_norm, hsp2', hsp0]) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h) (fun sf3 hpc3 hrun3 hsp3 hcs3 => ?_) (by dsimp only [stdDoInitSpec]; sep_frame)
      dsimp only [stdDoInitSpec]; wp_conv_pre => simp only [beq_self_eq_true, ↓reduceIte, sepConj_assoc]
      apply SepWP.pure_elim; intro hstd3; have hsp3' : sf3.sp = s0.sp - 32#64 := by simpa [wp_norm, arm64_norm, hsp2'] using hsp3
      rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs3 with ⟨hx19_3, hx20_3, c21, c22, c23, c24, c25, c26, c27, c28, _, cv⟩
      simp only [wp_norm, arm64_norm, hx20_2, b21, b22, b23, b24, b25, b26, b27, b28, bv] at hx19_3 hx20_3 c21 c22 c23 c24 c25 c26 c27 c28 cv; wp_steps 3
      refine SepWP.step_ldp64 (ea := s0.sp - 16#64) (ea2 := s0.sp - 8#64) (wb := none) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun3]) hf_13
        (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, wp_norm, arm64_norm, hsp3', hsp0]) (by simp [evalAddrMode, wp_norm, arm64_norm, hsp3', bv_lin_norm]) (by bv_lin) (by wp_sep_access) (by wp_sep_access) (by wp_norm_lhs) ?_
      refine SepWP.step_ldp64 (ea := s0.sp - 32#64) (ea2 := s0.sp - 24#64) (wb := some (.sp, s0.sp)) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun3]) hf_14
        (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, wp_norm, arm64_norm, hsp3', hsp0]) (by simp [evalAddrMode, wp_norm, arm64_norm, hsp3', bv_lin_norm]) (by bv_lin) (by wp_sep_access) (by wp_sep_access) (by wp_norm_lhs) ?_
      wp_step; apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun3]); refine ⟨fun hm => ?_, by simp [wp_norm, arm64_norm], ?_⟩
      · rw [sepConj_assoc, satisfies_pure_sepConj]
        rcases hstd1 with ⟨f1, t1, tp1, sa1, bk1, bs1, pm1, p1⟩; simp only [sig_pc, sig_w64, sig_mem, wp_norm, arm64_norm, hm2, hm1] at f1 t1 tp1 sa1 bk1 bs1 pm1 p1
        rcases hstd2 with ⟨f2, t2, tp2, sa2, bk2, bs2, pm2, p2⟩; simp only [sig_pc, sig_w64, sig_ps, wp_norm, arm64_norm, f1, t1, tp1, sa1, bk1, bs1, pm1, p1] at f2 t2 tp2 sa2 bk2 bs2 pm2 p2
        rcases hstd3 with ⟨f3, t3, tp3, sa3, bk3, bs3, pm3, p3⟩; simp only [sig_pc, sig_w64, sig_ps, wp_norm, arm64_norm, f2, t2, tp2, sa2, bk2, bs2, pm2, p2] at f3 t3 tp3 sa3 bk3 bs3 pm3 p3
        refine ⟨⟨by simp [wp_norm, arm64_norm, f3], by simp [wp_norm, arm64_norm, t3], by simp [wp_norm, arm64_norm, tp3], by simp [sig_pc, sig_w64, sig_ps, sa3], by simp [wp_norm, arm64_norm, bk3], by simp [wp_norm, arm64_norm, bs3], by simp [wp_norm, arm64_norm, pm3], fun a => by simp [wp_norm, arm64_norm, p3]⟩, ?_⟩
        rw [stackFrameAt_split s0.sp 0x20 0xe0, hsf20]; sep_frame
      · rw [CalleeSavedPreserved.iff_regs]; simp [wp_norm, arm64_norm, c21, c22, c23, c24, c25, c26, c27, c28, cv]
private theorem sxtw_shl3_add8_eq {argc : Nat} (hargc : argc < 2 ^ 31) : BitVec.signExtend 64 (BitVec.ofNat 32 argc) <<< 3 + 8#64 = BitVec.ofNat 64 (8 * (argc + 1)) := by
  let v := BitVec.ofNat 64 argc; have hv_lt : v.ult 0x80000000#64 = true := by simp only [v, BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; omega
  have hv_tr : v.truncate 32 = BitVec.ofNat 32 argc := by apply BitVec.eq_of_toNat_eq; simp [v]
  have hv_se : BitVec.signExtend 64 (v.truncate 32) = v := by revert hv_lt; bv_bits
  rw [← hv_tr, hv_se]; apply BitVec.eq_of_toNat_eq; simp [v, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

/-- Symbolic `SepWP` stepping lemma for `libc_start_main_stage2` (`+0x000..+0x034`), pushing the `0x30`
    stack frame, running `libc_start_init`, and invoking `blr x21` to enter `L.cMainAddr` (`x30 = +0x38`). -/
theorem stage2_to_cMain (P : Program) (L : StdBinaryLayout) (hc : hasInstrs P L.libcStartMainStage2Addr (libcStartMainStage2EntryInstrs L))
    (hLibcStartInit : subroutine_ok P L.libcStartInitAddr (stdLibcStartInitSpec L))
    {target_pc sp0 argvTableAddr hwcap hwcap2 auxvAddr : BitVec 64} {argc : Nat} {entries : List (BitVec 64 × BitVec 64)}
    {s0 : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s0.pc = L.libcStartMainStage2Addr) (hrun : s0.status = .Running) (hsp : s0.sp = sp0) (hsp_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = L.cMainAddr) (hx1 : s0.readReg32 .x1 = BitVec.ofNat 32 argc) (hx2 : s0.readReg64 .x2 = argvTableAddr) (hargc : argc < 2 ^ 31)
    (hhwcap : hwcap &&& 0x3#64 = 0x3#64) (hnonull : ∀ t v, (t, v) ∈ entries → t ≠ 0#64)
    (hfind16 : entries.find? (·.1 == 16#64) = some (16#64, hwcap)) (hfind26 : entries.find? (·.1 == 26#64) = some (26#64, hwcap2)) (hbound : L.initArrayAddr.toNat + 16 < 2 ^ 64)
    (hnext : ∀ sf : State, sf.pc = L.cMainAddr → sf.status = .Running → sf.sp = sp0 - 0x30#64 → sf.spAligned = true →
      sf.readReg64 .x30 = L.libcStartMainStage2Addr + 0x38#64 → sf.readReg64 .x0 = BitVec.ofNat 64 argc → sf.readReg64 .x1 = argvTableAddr →
      sf.readReg64 .x2 = argvTableAddr + BitVec.ofNat 64 (8 * (argc + 1)) → StdStatePreserved s0 sf →
      SepWP P target_pc sf ((stdInitGlobalsPost L hwcap auxvAddr entries ∗ stackFrameAt sp0 0x30 ∗ stackFrameAt (sp0 - 0x30#64) 0x100) ∗ F) post oom) :
    SepWP P target_pc s0 ((stdInitGlobalsPre L auxvAddr entries ∗ stackFrameAt sp0 0x130) ∗ F) post oom := by
  have hsp0r : s0.readReg64 .sp = sp0 := hsp; have hsp0 : sp0 &&& 15#64 = 0#64 := hsp ▸ sp_and_15_of_spAligned hsp_align
  have hx0' : s0.readReg64 (.gpr 0#5) = L.cMainAddr := hx0; have hx2' : s0.readReg64 (.gpr 2#5) = argvTableAddr := hx2
  have hx1' : (s0.readReg64 (.gpr 1#5)).truncate 32 = BitVec.ofNat 32 argc := hx1
  have hsf30 : stackFrameAt sp0 0x30 = (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
      ((sp0 - 48#64) ↦₆₄ w0) ∗ ((sp0 - 40#64) ↦₆₄ w1) ∗ ((sp0 - 32#64) ↦₆₄ w2) ∗ ((sp0 - 24#64) ↦₆₄ w3) ∗ ((sp0 - 16#64) ↦₆₄ w4) ∗ ((sp0 - 8#64) ↦₆₄ w5)) := by simp [stackFrameAt, stackFrameSlotsFrom, stackFrameSlotsCont]
  wp_conv_pre => dsimp only [stdInitGlobalsPre]; rw [stackFrameAt_split sp0 0x30 0x100, hsf30]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1; apply SepWP.exists_elim; intro w2
  apply SepWP.exists_elim; intro w3; apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5; have_instrs hc 0 14; clear hc
  refine step_stp64_perm (ea := sp0 - 48#64) (ea2 := sp0 - 40#64) (v1 := s0.readReg64 (.gpr 29#5)) (v2 := s0.readReg64 (.gpr 30#5)) (wb := some (.sp, sp0 - 48#64)) hpc hrun hf_0
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hsp_align]) (by simp [evalAddrMode, hsp0r, bv_lin_norm]) (by bv_lin) rfl rfl (by wp_sep_access) (by wp_sep_access) fun m1 hm1 => ?_
  wp_step; refine step_stp64_perm (ea := sp0 - 16#64) (ea2 := sp0 - 8#64) (v1 := s0.readReg64 (.gpr 21#5)) (v2 := s0.readReg64 (.gpr 22#5)) (wb := none) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) hf_2
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, wp_norm, arm64_norm, hsp0]) (by simp [evalAddrMode, wp_norm, arm64_norm, bv_lin_norm]) (by bv_lin) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by wp_sep_access) (by wp_sep_access) fun m2 hm2 => ?_
  wp_steps 3; refine step_stp64_perm (ea := sp0 - 32#64) (ea2 := sp0 - 24#64) (v1 := s0.readReg64 (.gpr 19#5)) (v2 := s0.readReg64 (.gpr 20#5)) (wb := none) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) hf_6
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, wp_norm, arm64_norm, hsp0]) (by simp [evalAddrMode, wp_norm, arm64_norm, bv_lin_norm]) (by bv_lin) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by wp_sep_access) (by wp_sep_access) fun m3 hm3 => ?_
  wp_steps 3; refine SepWP.let_sp (sp' := sp0 - 48#64) (by simp [wp_norm, arm64_norm]) fun hsp_bl => ?_
  refine SepWP.call_subroutine_frame_auto hLibcStartInit (x := (hwcap, hwcap2, auxvAddr, entries)) (ret_pc := L.libcStartMainStage2Addr + 0x28#64) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (by simp [State.spAligned, wp_norm, arm64_norm, hsp0]) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 => ?_) (by dsimp only [stdLibcStartInitSpec, stdInitGlobalsPre]; rw [hsp_bl]; sep_frame (disch := assumption))
  dsimp only [stdLibcStartInitSpec, stdInitGlobalsPost]; wp_conv_pre => rw [hsp_bl, sepConj_assoc]
  apply SepWP.pure_elim; intro hstd1; wp_conv_pre => simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro cacheVal; have hsp1' : sf1.sp = sp0 - 48#64 := hsp1.trans hsp_bl
  rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs1 with ⟨g19, g20, g21, g22, _⟩; simp only [wp_norm, arm64_norm] at g19 g20 g21 g22
  rcases hstd1 with ⟨f1, t1, tp1, sa1, bk1, bs1, pm1, p1⟩; simp only [sig_pc, sig_w64, sig_mem, wp_norm, arm64_norm, hm3, hm2, hm1] at f1 t1 tp1 sa1 bk1 bs1 pm1 p1; wp_steps 3; wp_step
  refine SepWP.weaken_pre ?_ (hnext _ (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1]) (by simp [wp_norm, arm64_norm, hsp1'])
    (by simp [State.spAligned, wp_norm, arm64_norm, hsp1', hsp0]) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by apply BitVec.eq_of_toNat_eq; simp [wp_norm, arm64_norm]; omega) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, BitVec.add_assoc, sxtw_shl3_add8_eq hargc])
    ⟨by simp [wp_norm, arm64_norm, f1], by simp [wp_norm, arm64_norm, t1], by simp [wp_norm, arm64_norm, tp1], by simp [sig_pc, sig_w64, sa1], by simp [wp_norm, arm64_norm, bk1], by simp [wp_norm, arm64_norm, bs1], by simp [wp_norm, arm64_norm, pm1], fun a => by simp [wp_norm, arm64_norm, p1]⟩)
  dsimp only [stdInitGlobalsPost]; rw [hsf30]; sep_frame
end
end ProofLib.StdStartup

