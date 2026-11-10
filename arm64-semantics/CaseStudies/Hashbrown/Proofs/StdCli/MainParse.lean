/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.StdCli.Lib
public import CaseStudies.Hashbrown.Proofs.StdCli.Stdout
public import CaseStudies.Hashbrown.Proofs.StdCli.MainPure
public import ProofLib.SepLogic.WPFrozen
public meta import ProofLib.LiteralFetchLint

/-!
# Command-Loop Code Bundle, Call Wrappers, and Parsers

Placement-generic symbolic code bundle (`HbMainCmdCode`), `WordTree` validator, budget and call
wrappers, and `SepWP` specifications for the pure-CPU parsers and `hashbrown_cli::parse_command`.
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs.StdCli

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.StdStartup ProofLib.ProgramReflection
open CaseStudies.Hashbrown CaseStudies.Hashbrown.Proofs

/-! ## Symbolic code bundle and `WordTree` validator -/

local macro "iAdr " rd:term:arg pc:term:arg t:term:arg : term =>
  `(Instr.adr false $rd ($t - $pc))
local macro "iBl " pc:term:arg t:term:arg : term =>
  `(Instr.bl ($t - $pc))

def hbBytesEqWords : List (BitVec 32) :=
  [0xeb03003f#32, 0x54000161#32, 0xf100003f#32, 0x1a9f17e8#32, 0xb40000c1#32,
   0x38401409#32, 0xd1000421#32, 0x3840144a#32, 0x6b0a013f#32, 0x54ffff20#32,
   0x2a0803e0#32, 0xd65f03c0#32, 0x2a1f03e8#32, 0x2a0803e0#32, 0xd65f03c0#32]

def hbBytesEqChunks (C : HbCliLayout) : List CodeChunk :=
  [.words C.bytesEqAddr hbBytesEqWords]

def hbStripPrefixChunks (C : HbCliLayout) : List CodeChunk :=
  let s := C.stripPrefixAddr
  [ .words s
      [0xa9bd7bfd#32, 0xf9000bf5#32, 0xa9024ff4#32, 0x910003fd#32, 0xeb030033#32,
       0x54000103#32, 0xaa0303e1#32, 0xaa0303f4#32, 0xaa0003f5#32],
    .instrs s 0x24 [iBl (s + 0x24#64) C.bytesEqAddr],
    .words (s + 0x28#64)
      [0x36000060#32, 0x8b1402a0#32, 0x14000002#32, 0xaa1f03e0#32, 0xaa1303e1#32,
       0xa9424ff4#32, 0xf9400bf5#32, 0xa8c37bfd#32, 0xd65f03c0#32] ]

def hbSplitOnceSpaceWords : List (BitVec 32) :=
  [0xb4000101#32, 0xaa1f03e9#32, 0x3869680a#32, 0x7100815f#32, 0x540000c0#32,
   0x91000529#32, 0xeb09003f#32, 0x54ffff61#32, 0xf900011f#32, 0xd65f03c0#32,
   0xeb09003f#32, 0x54000062#32, 0xf900011f#32, 0xd65f03c0#32, 0x54000061#32,
   0xf900011f#32, 0xd65f03c0#32, 0x8b09000a#32, 0xaa2903eb#32, 0xa9002500#32,
   0x91000549#32, 0x8b01016a#32, 0xa9012909#32, 0xd65f03c0#32]

def hbSplitOnceSpaceChunks (C : HbCliLayout) : List CodeChunk :=
  [.words C.splitOnceSpaceAddr hbSplitOnceSpaceWords]

def hbParseDecimalU64Words : List (BitVec 32) :=
  [0xb40002a1#32, 0xaa0103e8#32, 0xaa1f03e1#32, 0x5280014a#32, 0xb4000288#32,
   0x38401409#32, 0x5100c12b#32, 0x7100257f#32, 0x540001a8#32, 0x9bca7c2c#32,
   0x8b01082d#32, 0xaa1f03e9#32, 0xd37ff9ad#32, 0xeb0c03ff#32, 0x1a9f07ec#32,
   0xab2b01a1#32, 0x1a9f37eb#32, 0x370000ac#32, 0xd1000508#32, 0x3607fe2b#32,
   0x14000002#32, 0xaa1f03e9#32, 0xaa0903e0#32, 0xd65f03c0#32, 0x52800029#32,
   0xaa0903e0#32, 0xd65f03c0#32]

def hbParseDecimalU64Chunks (C : HbCliLayout) : List CodeChunk :=
  [.words C.parseDecimalU64Addr hbParseDecimalU64Words]

def hbParseCommandChunks (C : HbCliLayout) : List CodeChunk :=
  let p := C.parseCommandAddr
  [ .words p [0xd10143ff#32, 0xa9027bfd#32, 0xa90357f6#32, 0xa9044ff4#32, 0x910083fd#32, 0xd503201f#32],
    .instrs p 0x18 [iAdr .x2 (p + 0x18#64) C.pfxInsertAddr],
    .words (p + 0x1c#64) [0x528000e3#32, 0xaa0103f4#32, 0xaa0003f5#32, 0xaa0803f3#32],
    .instrs p 0x2c [iBl (p + 0x2c#64) C.stripPrefixAddr],
    .words (p + 0x30#64) [0xb4000220#32, 0x910003e8#32],
    .instrs p 0x38 [iBl (p + 0x38#64) C.splitOnceSpaceAddr],
    .words (p + 0x3c#64) [0xf94003e0#32, 0xb4000ae0#32, 0xa940d7e1#32, 0xf9400ff6#32],
    .instrs p 0x4c [iBl (p + 0x4c#64) C.parseDecimalU64Addr],
    .words (p + 0x50#64) [0x36000a60#32, 0xaa0103f4#32, 0xaa1503e0#32, 0xaa1603e1#32],
    .instrs p 0x60 [iBl (p + 0x60#64) C.parseDecimalU64Addr],
    .words (p + 0x64#64) [0x360009c0#32, 0xa900527f#32, 0xf9000a61#32, 0x1400004d#32, 0xd503201f#32],
    .instrs p 0x78 [iAdr .x2 (p + 0x78#64) C.pfxRemoveAddr],
    .words (p + 0x7c#64) [0xaa1503e0#32, 0xaa1403e1#32, 0x528000e3#32],
    .instrs p 0x88 [iBl (p + 0x88#64) C.stripPrefixAddr],
    .words (p + 0x8c#64) [0xb40000a0#32],
    .instrs p 0x90 [iBl (p + 0x90#64) C.parseDecimalU64Addr],
    .words (p + 0x94#64) [0x36000840#32, 0x52800048#32, 0x14000016#32, 0xd503201f#32],
    .instrs p 0xa4 [iAdr .x2 (p + 0xa4#64) C.pfxGetAddr],
    .words (p + 0xa8#64) [0xaa1503e0#32, 0xaa1403e1#32, 0x52800083#32],
    .instrs p 0xb4 [iBl (p + 0xb4#64) C.stripPrefixAddr],
    .words (p + 0xb8#64) [0xb40000a0#32],
    .instrs p 0xbc [iBl (p + 0xbc#64) C.parseDecimalU64Addr],
    .words (p + 0xc0#64) [0x360006e0#32, 0x52800028#32, 0x1400000b#32, 0xd503201f#32],
    .instrs p 0xd0 [iAdr .x2 (p + 0xd0#64) C.pfxContainsAddr],
    .words (p + 0xd4#64) [0xaa1503e0#32, 0xaa1403e1#32, 0x52800123#32],
    .instrs p 0xe0 [iBl (p + 0xe0#64) C.stripPrefixAddr],
    .words (p + 0xe4#64) [0xb40000c0#32],
    .instrs p 0xe8 [iBl (p + 0xe8#64) C.parseDecimalU64Addr],
    .words (p + 0xec#64) [0x36000580#32, 0x52800068#32, 0xa9000668#32, 0x1400002b#32, 0xd503201f#32],
    .instrs p 0x100 [iAdr .x2 (p + 0x100#64) C.pfxWithCapAddr],
    .words (p + 0x104#64) [0xaa1503e0#32, 0xaa1403e1#32, 0x528001c3#32],
    .instrs p 0x110 [iBl (p + 0x110#64) C.stripPrefixAddr],
    .words (p + 0x114#64) [0xb40000e0#32],
    .instrs p 0x118 [iBl (p + 0x118#64) C.parseDecimalU64Addr],
    .words (p + 0x11c#64) [0x36000400#32, 0xf140043f#32, 0x540003c8#32, 0x52800088#32, 0x17fffff2#32, 0xd503201f#32],
    .instrs p 0x134 [iAdr .x2 (p + 0x134#64) C.cmdLenAddr],
    .words (p + 0x138#64) [0xaa1503e0#32, 0xaa1403e1#32, 0x52800063#32],
    .instrs p 0x144 [iBl (p + 0x144#64) C.bytesEqAddr],
    .words (p + 0x148#64) [0x36000060#32, 0x528000a8#32, 0x14000014#32, 0xd503201f#32],
    .instrs p 0x158 [iAdr .x2 (p + 0x158#64) C.cmdIsEmptyAddr],
    .words (p + 0x15c#64) [0xaa1503e0#32, 0xaa1403e1#32, 0x52800103#32],
    .instrs p 0x168 [iBl (p + 0x168#64) C.bytesEqAddr],
    .words (p + 0x16c#64) [0x36000060#32, 0x528000c8#32, 0x1400000b#32, 0xd503201f#32],
    .instrs p 0x17c [iAdr .x2 (p + 0x17c#64) C.cmdClearAddr],
    .words (p + 0x180#64) [0xaa1503e0#32, 0xaa1403e1#32, 0x528000a3#32],
    .instrs p 0x18c [iBl (p + 0x18c#64) C.bytesEqAddr],
    .words (p + 0x190#64)
      [0x36000060#32, 0x528000e8#32, 0x14000002#32, 0x92800008#32, 0xf9000268#32,
       0xa9444ff4#32, 0xa94357f6#32, 0xa9427bfd#32, 0x910143ff#32, 0xd65f03c0#32] ]
def hbNlScanWords : List (BitVec 32) :=
  [0xaa1f03e1#32, 0xb4000176#32, 0x38616808#32, 0x7100291f#32, 0x54000160#32,
   0x91000421#32, 0xeb0102df#32, 0x54ffff61#32, 0x5280003a#32, 0xaa1603e1#32,
   0xaa0003fb#32, 0x14000009#32, 0x5280003a#32, 0xaa0003fb#32, 0x14000006#32,
   0xaa2103e8#32, 0x8b010009#32, 0x2a1f03fa#32, 0x8b160116#32, 0x9100053b#32]

/-- Reachable symbolic code chunks for `hashbrown_cli::main` from `u + 0x13c` through `u + 0x310`
    (`u := C.std.userMainAddr`, omitting dead `+0x238..+0x260`). -/
def hbRustMainLoopChunks (C : HbCliLayout) : List CodeChunk :=
  let u := C.std.userMainAddr
  [ .words (u + 0x13c#64) [0x910083e8#32, 0xaa0903f3#32],
    .instrs u 0x144 [iBl (u + 0x144#64) (hashbrownLib.fnAddr C.hbMpl "hashbrown_new")],
    .words (u + 0x148#64) [0xaa1303e0#32, 0xd503201f#32],
    .instrs u 0x150 [iAdr .x23 (u + 0x150#64) C.stderrGlobalAddr],
    .words (u + 0x154#64) [0xd10083b8#32, 0xd503201f#32],
    .instrs u 0x15c [iAdr .x19 (u + 0x15c#64) C.errInvalidCmdAddr],
    .words (u + 0x160#64) [0x52800079#32, 0xd503201f#32],
    .instrs u 0x168 [iAdr .x20 (u + 0x168#64) C.noneNlAddr],
    .words (u + 0x16c#64) [0x14000006#32, 0xf85d03a1#32, 0x910083e0#32],
    .instrs u 0x178 [iBl (u + 0x178#64) (hashbrownLib.fnAddr C.hbMpl "hashbrown_remove")],
    .words (u + 0x17c#64) [0xaa1b03e0#32, 0x37000c1a#32],
    .words (u + 0x184#64) hbNlScanWords,
    .words (u + 0x1d4#64) [0xd100e3a8#32],
    .instrs u 0x1d8 [iBl (u + 0x1d8#64) C.parseCommandAddr],
    .words (u + 0x1dc#64)
      [0xf85c83a8#32, 0xf100091f#32, 0x5400016d#32, 0xf100111f#32, 0x540004cd#32,
       0x910083e0#32, 0xf100151f#32, 0x54000540#32, 0xf100191f#32, 0x540005e1#32],
    .instrs u 0x204
      [ iBl (u + 0x204#64) (hashbrownLib.fnAddr C.hbMpl "hashbrown_is_empty"),
        iBl (u + 0x208#64) C.printBoolAddr ],
    .words (u + 0x20c#64)
      [0x17ffffdc#32, 0xf100011f#32, 0x5400028c#32, 0xb100051f#32, 0x54000481#32,
       0x910063a0#32, 0xaa1303e1#32, 0x528002e2#32, 0xf9000fb7#32],
    .instrs u 0x230 [iBl (u + 0x230#64) C.stderrWriteAllAddr],
    .words (u + 0x234#64) [0xb4fffa40#32],
    .words (u + 0x264#64) [0xf100051f#32, 0x54fff841#32, 0xf85d03a1#32, 0x910083e0#32],
    .instrs u 0x274 [iBl (u + 0x274#64) (hashbrownLib.fnAddr C.hbMpl "hashbrown_get")],
    .words (u + 0x278#64)
      [0x360003c0#32, 0xaa0103e0#32, 0x14000009#32, 0xf1000d1f#32, 0x540001e1#32,
       0xf85d03a1#32, 0x910083e0#32],
    .instrs u 0x294
      [ iBl (u + 0x294#64) (hashbrownLib.fnAddr C.hbMpl "hashbrown_contains_key"),
        iBl (u + 0x298#64) C.printBoolAddr ],
    .words (u + 0x29c#64) [0x17ffffb8#32],
    .instrs u 0x2a0
      [ iBl (u + 0x2a0#64) (hashbrownLib.fnAddr C.hbMpl "hashbrown_len"),
        iBl (u + 0x2a4#64) C.printU64Addr ],
    .words (u + 0x2a8#64) [0x17ffffb5#32, 0xa97d0ba1#32, 0x910083e0#32],
    .instrs u 0x2b4 [iBl (u + 0x2b4#64) (hashbrownLib.fnAddr C.hbMpl "hashbrown_insert")],
    .words (u + 0x2b8#64) [0x17ffffb1#32],
    .instrs u 0x2bc [iBl (u + 0x2bc#64) (hashbrownLib.fnAddr C.hbMpl "hashbrown_clear")],
    .words (u + 0x2c0#64)
      [0x17ffffaf#32, 0xad4107e0#32, 0xd10083a0#32, 0xf85d03b5#32, 0xad3f07a0#32],
    .instrs u 0x2d4 [iBl (u + 0x2d4#64) (hashbrownLib.fnAddr C.hbMpl "hashbrown_drop")],
    .words (u + 0x2d8#64) [0xd10083a8#32, 0xaa1503e0#32],
    .instrs u 0x2e0 [iBl (u + 0x2e0#64) (hashbrownLib.fnAddr C.hbMpl "hashbrown_with_capacity")],
    .words (u + 0x2e4#64) [0xad7f07a0#32, 0xad0107e0#32, 0x17ffffa4#32, 0xaa1403e0#32, 0x52800161#32],
    .instrs u 0x2f8 [iBl (u + 0x2f8#64) C.stdioPrintAddr],
    .words (u + 0x2fc#64) [0x17ffffa0#32, 0xad4107e0#32, 0xd10083a0#32, 0xad3f07a0#32],
    .instrs u 0x30c [iBl (u + 0x30c#64) (hashbrownLib.fnAddr C.hbMpl "hashbrown_drop")] ]

/-- Full symbolic code bundle for `bytesEq`, `stripPrefix`, `splitOnceSpace`, `parseDecimalU64`,
    `parseCommand`, and the `rustMain` command-loop segment (`+0x13c .. +0x310`). -/
def hbMainCmdChunks (C : HbCliLayout) : List CodeChunk :=
  hbBytesEqChunks C ++
  (hbStripPrefixChunks C ++
  (hbSplitOnceSpaceChunks C ++
  (hbParseDecimalU64Chunks C ++
  (hbParseCommandChunks C ++
  hbRustMainLoopChunks C))))

abbrev HbMainCmdCode (P : Program) (C : HbCliLayout) : Prop :=
  CodeChunks P (hbMainCmdChunks C)

theorem HbMainCmdCode.withSvc {P : Program} {C : HbCliLayout} (svc : State → State)
    (h : HbMainCmdCode P C) :
    HbMainCmdCode (P.withSvc svc) C :=
  codeChunks_withSvc svc h

private theorem codeChunks_append {P : Program} :
    ∀ {xs ys : List CodeChunk}, CodeChunks P (xs ++ ys) → CodeChunks P xs ∧ CodeChunks P ys
  | [], _, h => ⟨trivial, h⟩
  | [_], [], h => ⟨h, trivial⟩
  | [_], _ :: _, ⟨h1, h2⟩ => ⟨h1, h2⟩
  | _ :: x2 :: xs, ys, ⟨h1, h2⟩ =>
    let ⟨ha, hb⟩ := codeChunks_append (xs := x2 :: xs) (ys := ys) h2
    ⟨⟨h1, ha⟩, hb⟩

theorem HbMainCmdCode.bytesEq {P : Program} {C : HbCliLayout} (h : HbMainCmdCode P C) :
    CodeChunks P (hbBytesEqChunks C) := (codeChunks_append h).1

theorem HbMainCmdCode.stripPrefix {P : Program} {C : HbCliLayout} (h : HbMainCmdCode P C) :
    CodeChunks P (hbStripPrefixChunks C) := (codeChunks_append (codeChunks_append h).2).1

theorem HbMainCmdCode.splitOnceSpace {P : Program} {C : HbCliLayout} (h : HbMainCmdCode P C) :
    CodeChunks P (hbSplitOnceSpaceChunks C) :=
  (codeChunks_append (codeChunks_append (codeChunks_append h).2).2).1

theorem HbMainCmdCode.parseDecimalU64 {P : Program} {C : HbCliLayout} (h : HbMainCmdCode P C) :
    CodeChunks P (hbParseDecimalU64Chunks C) :=
  (codeChunks_append (codeChunks_append (codeChunks_append (codeChunks_append h).2).2).2).1

theorem HbMainCmdCode.parseCommand {P : Program} {C : HbCliLayout} (h : HbMainCmdCode P C) :
    CodeChunks P (hbParseCommandChunks C) :=
  (codeChunks_append (codeChunks_append (codeChunks_append (codeChunks_append
    (codeChunks_append h).2).2).2).2).1

theorem HbMainCmdCode.rustMainLoop {P : Program} {C : HbCliLayout} (h : HbMainCmdCode P C) :
    CodeChunks P (hbRustMainLoopChunks C) :=
  (codeChunks_append (codeChunks_append (codeChunks_append (codeChunks_append
    (codeChunks_append h).2).2).2).2).2

private theorem hbMainCmdChunks_of_check {P : Program} {b : BitVec 64} {t : WordTree}
    (hc : ∀ {c : CodeChunk}, checkCodeChunk b t c = true → c.holds P) :
    ∀ {cs : List CodeChunk}, cs.all (checkCodeChunk b t) = true → CodeChunks P cs
  | [], _ => trivial
  | [_], h => hc (by simpa using h)
  | _ :: _ :: _, h => by
    rw [List.all_cons, Bool.and_eq_true] at h
    exact ⟨hc h.1, hbMainCmdChunks_of_check hc h.2⟩

/-- Boolean `WordTree` validator for `HbMainCmdCode`. -/
def checkHbMainCmdCode (C : HbCliLayout) (base : BitVec 64) (t : WordTree) : Bool :=
  (hbMainCmdChunks C).all (checkCodeChunk base t)

theorem hbMainCmdCode_of_wordTree {P : Program} {C : HbCliLayout} {t : WordTree}
    (n : Nat) (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hstubs : P.stubs = [] := by rfl) (hsyms : P.symbols = [] := by rfl)
    (hext : ∀ sym, (P.externs sym).isNone = true := by intro _; rfl)
    (hovr : ∀ sym, (P.overrides sym).isNone = true := by intro _; rfl)
    (hok : checkHbMainCmdCode C P.base t = true) :
    HbMainCmdCode P C := by
  have hc : ∀ {c : CodeChunk}, checkCodeChunk P.base t c = true → c.holds P := by
    rintro (⟨a, ws⟩ | ⟨b, is⟩ | ⟨b, o, is⟩) h
    · simp only [checkCodeChunk, checkCleanupWordsAt, Bool.and_eq_true, decide_eq_true_eq] at h
      exact hasWords_of_wordTree n hcode hwf rfl h.1 hstubs hsyms h.2
    all_goals
      simp only [checkCodeChunk, checkCleanupInstrsAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      exact hasInstrs_of_wordTree n hcode hwf h.1.1 h.1.2 hext hovr h.2
  exact hbMainCmdChunks_of_check hc hok

/-! ## Cut combinators, budget arithmetic, and call wrappers -/

local macro "unpack_stdout_code " chunks:ident h:term : tactic => `(tactic| (
  have _hc := stdoutToStepFacts $h
  simp only [$chunks:ident, stdoutStepFacts, stdoutStepAcc, fetchAtAcc',
    Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at _hc
  (repeat obtain ⟨_, _hc⟩ := _hc); try clear _hc))

local macro "norm_jmp" : tactic =>
  `(tactic| conv in State.setPC _ _ => arg 2; rw [bv64_add_sub_cancel])
local macro "close_cs" : tactic =>
  `(tactic| simp [CalleeSavedPreserved.iff_regs, Reg.fp, wp_norm, arm64_norm, *])
local macro "wp_a" : term => `(by simp [wp_norm, arm64_norm, bv_lin_norm, *]; try bv_lin)

attribute [local simp] cpuAux_writeReg64 cpuAux_writeReg32 cpuAux_writeReg
  cpuAux_setPState cpuAux_advancePC cpuAux_setPC cpuAux_setMem

theorem sepWP_cpu_cut {P : Program} {mid target : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {CodeInv : Memory → Prop}
    (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    (hCode : CodeInv s.mem)
    (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard)
    (h : SepWP (P.withSvc nonVmSvc) mid s Pre
      (fun sm Pm => VmFieldsPreserved s sm → CodeInv sm.mem → SepWP P target sm Pm post)) :
    SepWP P target s Pre post :=
  SepWP.seq_frozen (mid := mid) (Φ := CodeInv) (fun _ _ h0 hm => hCodeInv hm h0) hCode
    (SepWP.of_nonVm hext hsvc h)

theorem sepWP_frozen_cut {P : Program} {mid target : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {CodeInv : Memory → Prop}
    (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    (hCode : CodeInv s.mem)
    (h : SepWP P mid s Pre (fun sm Pm => CodeInv sm.mem → SepWP P target sm Pm post)) :
    SepWP P target s Pre post :=
  SepWP.seq_frozen (mid := mid) (Φ := CodeInv) (fun _ _ h0 hm => hCodeInv hm h0) hCode h

theorem max_le_add_r (a b : Nat) : max a b ≤ a + b :=
  Nat.max_le.mpr ⟨Nat.le_add_right a b, Nat.le_add_left b a⟩

theorem add_mid_sub_cancel (a b c : Nat) : (a + b + c) - b = a + c := by
  rw [Nat.add_right_comm, Nat.add_sub_cancel]

private theorem hbCli_print_arith {L vecCap lc cm blk : Nat}
    (hvec : vecCap ≤ 2 * L + 32)
    (hlc : lc ≤ 65536 + (if vecCap = 0 then 0 else max vecCap 65536) + cm)
    (hcm : cm ≤ 139272 ∨ 11 * cm ≤ 51 * L + 11 * 65552)
    (hblk : blk ≤ 3) :
    1024 ≤ (272 * L) / 77 + 139272 ∧
    lc + 65536 ≤ (562 * L) / 77 + 336000 ∧
    blk + 1 ≤ 5 := by
  have hv : (if vecCap = 0 then 0 else max vecCap 65536) ≤ 2 * L + 65536 := by split <;> omega
  exact ⟨by omega, by omega, by omega⟩

theorem hbCli_print_budget {P : Program} {addrs : MallocngAddrs} {L : Nat}
    (M : MallocngCoreIface P addrs (hbStdLimits L)) (γ : GhostName)
    (CodeInv : Memory → Prop)
    (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    {bm : BitVec 64} {k_ins vecCap lc blk : Nat}
    (_hL : L ≤ HashbrownCliMaxStdin) (hins : 11 * k_ins ≤ L + 1)
    (_hbm_wf : bm = 0#64 ∨ ValidBucketMask bm)
    (hbm_bound : bm ≠ 0#64 → bm.toNat + 1 ≤ max 8192 (3 * k_ins))
    (hvec : vecCap ≤ 2 * L + 32)
    (hlc : lc ≤ mallocngBlockCost 8192 +
                (if vecCap = 0 then 0 else mallocngBlockCost vecCap) +
                hbMapCost (HbAlloc.ofMallocng M γ CodeInv hCodeInv) bm)
    (hblk : blk ≤ 3) :
    1024 ≤ (hbStdLimits L).maxReq ∧
    lc + mallocngBlockCost 1024 ≤ (hbStdLimits L).maxPeakCost ∧
    blk + 1 ≤ (hbStdLimits L).maxPeakBlocks := by
  let A := HbAlloc.ofMallocng M γ CodeInv hCodeInv
  have h8192 : mallocngBlockCost 8192 = 65536 := by decide
  have h1024 : mallocngBlockCost 1024 = 65536 := by decide
  have hcm : hbMapCost A bm ≤ 139272 ∨ 11 * hbMapCost A bm ≤ 51 * L + 11 * 65552 := by
    by_cases hbm0 : bm = 0#64
    · rw [hbm0, hbMapCost_zero]; exact Or.inl (Nat.zero_le _)
    · have hb1 := hbm_bound hbm0
      unfold hbMapCost tableAllocBytes; simp only [hbm0, ↓reduceIte]
      dsimp only [A, HbAlloc.ofMallocng, mallocngBlockCost, MallocngMinBlockCost]
      by_cases hle8 : bm.toNat + 1 ≤ 8192
      · left; clear A hlc hbm_bound hCodeInv CodeInv γ M addrs P; omega
      · right
        have hmle := max_le_add_r (17 * (bm.toNat + 1) + 8) 65536
        clear A hlc hbm_bound hCodeInv CodeInv γ M addrs P; omega
  have hlc' : lc ≤ 65536 + (if vecCap = 0 then 0 else max vecCap 65536) + hbMapCost A bm := by
    rw [h8192] at hlc
    simpa only [mallocngBlockCost, MallocngMinBlockCost] using hlc
  rw [h1024]
  exact hbCli_print_arith hvec hlc' hcm hblk

theorem memRegion32_to_qpair (a : BitVec 64) :
    memRegion a 32 ⊢
      ∃∗ q0 : BitVec 128, ∃∗ q1 : BitVec 128, (a ↦₁₂₈ q0) ∗ ((a + 16#64) ↦₁₂₈ q1) := by
  rw [show (32 : Nat) = 16 + 16 from rfl, memRegion_split a 16 16 (by decide),
      show (16 : Nat) = 8 + 8 from rfl,
      memRegion_split a 8 8 (by decide), memRegion_split (a + 16#64) 8 8 (by decide),
      memRegion_eight a, memRegion_eight (a + 8#64),
      memRegion_eight (a + 16#64), memRegion_eight ((a + 16#64) + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro x3
  apply Entails.sepExists_elim; intro x2
  apply Entails.sepExists_elim; intro x1
  apply Entails.sepExists_elim; intro x0
  refine Entails.sepExists_right (x1 ++ x0) (Entails.sepExists_right (x3 ++ x2) ?_)
  rw [← pointsTo64_pair a x0 x1, ← pointsTo64_pair (a + 16#64) x2 x3]
  sep_entail

theorem qpair_to_memRegion32 (a : BitVec 64) (q0 q1 : BitVec 128) :
    (a ↦₁₂₈ q0) ∗ ((a + 16#64) ↦₁₂₈ q1) ⊢ memRegion a 32 := by
  rw [show (32 : Nat) = 16 + 16 from rfl, memRegion_split a 16 16 (by decide),
      show (16 : Nat) = 8 + 8 from rfl,
      memRegion_split a 8 8 (by decide), memRegion_split (a + 16#64) 8 8 (by decide),
      pointsTo128_split64 a q0, pointsTo128_split64 (a + 16#64) q1]
  exact sepConj_mono
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))

/-- Location-independent heap and metadata payload of `U64MapRep` while its 32-byte `U64MapStruct`
    `(q0, q1)` is moved in SIMD registers via `ldp q0, q1` / `stp q0, q1`. -/
def HbMapMoved (pl : Obj.Placement) (A : HbAlloc) (m : Map64) (bm : BitVec 64) (u : Nat)
    (q0 q1 : BitVec 128) : SepProp :=
  ⌜Map64Wf m⌝ ∗
  if bm = 0#64 then
    ⌜m = [] ∧ q0 = (0#64 : BitVec 64) ++ pl.ρ hbEmptyCtrlSym ∧
      q1 = (0#64 : BitVec 64) ++ (0#64 : BitVec 64)⌝ ∗ hbRodata pl
  else
    ∃∗ w : HbHeapMapWitness,
      ⌜SwissTableInv bm w.growthLeft w.items w.ctrl w.slots m ∧
       bucketMaskToCapacity bm - w.growthLeft.toNat ≤ u ∧
       w.allocPtr ≠ 0#64 ∧ w.allocPtr.toNat % 8 = 0 ∧
       w.allocPtr.toNat + (17 * (bm.toNat + 1) + 8) ≤ 2 ^ 64 ∧
       w.ctrlPtr = w.allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1)) ∧
       q0 = bm ++ w.ctrlPtr ∧ q1 = w.items ++ w.growthLeft⌝ ∗
      hbRodata pl ∗ A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗
      slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl)

private theorem u64MapStruct_eq_qpair (a c bm gl it : BitVec 64) :
    U64MapStruct a c bm gl it = ((a ↦₁₂₈ (bm ++ c)) ∗ ((a + 16#64) ↦₁₂₈ (it ++ gl))) := by
  unfold U64MapStruct
  rw [← pointsTo64_pair a c bm, ← pointsTo64_pair (a + 16#64) gl it,
      show (a + 16#64) + 8#64 = a + 24#64 by bv_lin]
  ac_rfl

theorem U64MapRep_unpack_qpair (pl : Obj.Placement) (A : HbAlloc) (src : BitVec 64)
    (m : Map64) (bm : BitVec 64) (u : Nat) :
    U64MapRep pl A src m bm u ⊢
      ∃∗ q0 : BitVec 128, ∃∗ q1 : BitVec 128,
        (src ↦₁₂₈ q0) ∗ ((src + 16#64) ↦₁₂₈ q1) ∗ HbMapMoved pl A m bm u q0 q1 := by
  unfold U64MapRep HbMapMoved
  apply Entails.pure_left; rintro ⟨_, _, hwf⟩
  by_cases h0 : bm = 0#64
  · simp only [h0, ↓reduceIte]
    rw [sepConj_left_comm (hbRodata pl)]; apply Entails.pure_left; intro hm
    refine Entails.sepExists_right ((0#64 : BitVec 64) ++ pl.ρ hbEmptyCtrlSym)
      (Entails.sepExists_right ((0#64 : BitVec 64) ++ (0#64 : BitVec 64)) ?_)
    rw [u64MapStruct_eq_qpair, pure_sepConj_of_true hwf, pure_sepConj_of_true ⟨hm, rfl, rfl⟩]
    sep_entail
  · simp only [h0, ↓reduceIte, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro w
    rw [sepConj_left_comm (hbRodata pl)]; apply Entails.pure_left; rintro ⟨h1, hu, h2, h3, h4, h5⟩
    refine Entails.sepExists_right (bm ++ w.ctrlPtr)
      (Entails.sepExists_right (w.items ++ w.growthLeft) (Entails.sepExists_right w ?_))
    rw [u64MapStruct_eq_qpair, pure_sepConj_of_true hwf,
        pure_sepConj_of_true ⟨h1, hu, h2, h3, h4, h5, rfl, rfl⟩]; sep_entail

theorem U64MapRep_repack_qpair (pl : Obj.Placement) (A : HbAlloc) {dst : BitVec 64}
    (m : Map64) (bm : BitVec 64) (u : Nat) (q0 q1 : BitVec 128)
    (hal : dst.toNat % 8 = 0) (hnw : dst.toNat + 32 ≤ 2 ^ 64) :
    (dst ↦₁₂₈ q0) ∗ ((dst + 16#64) ↦₁₂₈ q1) ∗ HbMapMoved pl A m bm u q0 q1 ⊢
      U64MapRep pl A dst m bm u := by
  unfold HbMapMoved U64MapRep
  rw [sepConj_left_comm ((dst + 16#64) ↦₁₂₈ q1), sepConj_left_comm (dst ↦₁₂₈ q0)]
  apply Entails.pure_left; intro hwf
  by_cases h0 : bm = 0#64
  · simp only [h0, ↓reduceIte]
    rw [sepConj_left_comm ((dst + 16#64) ↦₁₂₈ q1), sepConj_left_comm (dst ↦₁₂₈ q0)]
    apply Entails.pure_left; rintro ⟨rfl, rfl, rfl⟩
    rw [pure_sepConj_of_true ⟨hal, hnw, hwf⟩, u64MapStruct_eq_qpair, pure_sepConj_of_true rfl]
    sep_entail
  · simp only [h0, ↓reduceIte, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro w
    rw [sepConj_left_comm ((dst + 16#64) ↦₁₂₈ q1), sepConj_left_comm (dst ↦₁₂₈ q0)]
    apply Entails.pure_left; rintro ⟨h1, hu, h2, h3, h4, h5, rfl, rfl⟩
    refine Entails.sepExists_right w ?_
    rw [pure_sepConj_of_true ⟨hal, hnw, hwf⟩, u64MapStruct_eq_qpair,
        pure_sepConj_of_true ⟨h1, hu, h2, h3, h4, h5⟩]
    sep_entail

theorem call_hbNew {P : Program} {pl : Obj.Placement} {A : HbAlloc}
    {entry target_pc ret_pc mapPtr : BitVec 64} {s : State} {Pre F : SepProp}
    {post : State → SepProp → Prop}
    (hok : subroutine_ok P entry (withCodeInv A (hashbrownNewSpec pl A)))
    (hci : A.CodeInv s.mem) (hal : mapPtr.toNat % 8 = 0) (hfit : mapPtr.toNat + 32 ≤ 2 ^ 64)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_al : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (hx8 : s.readReg64 .x8 = mapPtr)
    (hpre : ∀ R, (s.mem ⊨ Pre ∗ R) → (s.mem ⊨ (hbRodata pl ∗ memRegion mapPtr 32) ∗ (F ∗ R)))
    (hnext : ∀ sf, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf → StdStatePreserved s sf → s.mem.KeepsFrozen sf.mem →
      SepWP P target_pc sf ((U64MapRep pl A mapPtr [] 0#64 0 ∗ hbRodata pl) ∗ F) post) :
    SepWP P target_pc s Pre post := by
  refine SepWP.call_subroutine_frame hok (x := mapPtr) (F := F)
    hpc hrun hsp_al hlr ?_ (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_ (by wp_close_oom_default)
  · intro R hm; dsimp only [withCodeInv, hashbrownNewSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hci, ?_⟩; rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hal, hfit⟩, hpre R hm⟩
  · intro sf hpc_f hrun_f hsp_f hcs_f; dsimp only [withCodeInv, hashbrownNewSpec]
    rw [sepConj_assoc]; apply SepWP.pure_elim; rintro ⟨_, hstd, hfz⟩
    exact hnext sf hpc_f hrun_f hsp_f hcs_f hstd hfz

theorem call_hbGet {P : Program} {pl : Obj.Placement} {A : HbAlloc}
    {entry target_pc ret_pc mapPtr bm k : BitVec 64} {m : Map64} {u : Nat} {s : State} {Pre F : SepProp}
    {post : State → SepProp → Prop}
    (hok : subroutine_ok P entry (withCodeInv A (hashbrownGetSpec pl A)))
    (hci : A.CodeInv s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_al : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx0 : s.readReg64 .x0 = mapPtr) (hx1 : s.readReg64 .x1 = k)
    (hpre : ∀ R, (s.mem ⊨ Pre ∗ R) → (s.mem ⊨ U64MapRep pl A mapPtr m bm u ∗ (F ∗ R)))
    (hnext : ∀ sf, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      (match cliMapLookup k m with
       | none   => sf.readReg64 .x0 = 0#64
       | some v => sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 = v) →
      StdStatePreserved s sf → s.mem.KeepsFrozen sf.mem →
      SepWP P target_pc sf (U64MapRep pl A mapPtr m bm u ∗ F) post) :
    SepWP P target_pc s Pre post := by
  refine SepWP.call_subroutine_frame hok (x := (mapPtr, m, bm, u, k)) (F := F)
    hpc hrun hsp_al hlr ?_ (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_ (by wp_close_oom_default)
  · intro R hm; dsimp only [withCodeInv, hashbrownGetSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hci, ?_⟩; rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1⟩, hpre R hm⟩
  · intro sf hpc_f hrun_f hsp_f hcs_f; dsimp only [withCodeInv, hashbrownGetSpec]
    rw [sepConj_assoc]; apply SepWP.pure_elim; rintro ⟨hres, hstd, hfz⟩
    exact hnext sf hpc_f hrun_f hsp_f hcs_f hres hstd hfz

theorem call_hbRemove {P : Program} {pl : Obj.Placement} {A : HbAlloc}
    {entry target_pc ret_pc mapPtr bm k : BitVec 64} {m : Map64} {u : Nat} {s : State} {Pre F : SepProp}
    {post : State → SepProp → Prop}
    (hok : subroutine_ok P entry (withCodeInv A (hashbrownRemoveSpec pl A)))
    (hci : A.CodeInv s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_al : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx0 : s.readReg64 .x0 = mapPtr) (hx1 : s.readReg64 .x1 = k)
    (hpre : ∀ R, (s.mem ⊨ Pre ∗ R) → (s.mem ⊨ U64MapRep pl A mapPtr m bm u ∗ (F ∗ R)))
    (hnext : ∀ sf, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf → StdStatePreserved s sf → s.mem.KeepsFrozen sf.mem →
      SepWP P target_pc sf (U64MapRep pl A mapPtr (cliMapErase k m) bm u ∗ F) post) :
    SepWP P target_pc s Pre post := by
  refine SepWP.call_subroutine_frame hok (x := (mapPtr, m, bm, u, k)) (F := F)
    hpc hrun hsp_al hlr ?_ (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_ (by wp_close_oom_default)
  · intro R hm; dsimp only [withCodeInv, hashbrownRemoveSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hci, ?_⟩; rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1⟩, hpre R hm⟩
  · intro sf hpc_f hrun_f hsp_f hcs_f; dsimp only [withCodeInv, hashbrownRemoveSpec]
    rw [sepConj_assoc]; apply SepWP.pure_elim; rintro ⟨_, hstd, hfz⟩
    exact hnext sf hpc_f hrun_f hsp_f hcs_f hstd hfz

theorem call_hbInsertInf {P : Program} {pl : Obj.Placement} {addrs : MallocngAddrs} {lim : MallocngLimits}
    (M : MallocngCoreIface P addrs lim) (γ : GhostName)
    (CodeInv : Memory → Prop)
    (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    {entry target_pc ret_pc mapPtr bm k v : BitVec 64} {m : Map64} {u lc0 blk0 : Nat} {e0 : BitVec 32}
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop}
    (hok : subroutine_ok P entry
      (withCodeInv (HbAlloc.ofMallocng M γ CodeInv hCodeInv)
        (hashbrownInsertInfallibleSpec pl (HbAlloc.ofMallocng M γ CodeInv hCodeInv))))
    (hci : CodeInv s.mem)
    (hcan : HbCanInsertOne (HbAlloc.ofMallocng M γ CodeInv hCodeInv) m bm u
      (lc0 + hbMapCost (HbAlloc.ofMallocng M γ CodeInv hCodeInv) bm)
      (blk0 + tableAllocBlocks bm))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_al : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx0 : s.readReg64 .x0 = mapPtr) (hx1 : s.readReg64 .x1 = k) (hx2 : s.readReg64 .x2 = v)
    (hpre : ∀ R, (s.mem ⊨ Pre ∗ R) →
      (s.mem ⊨ (U64MapRep pl (HbAlloc.ofMallocng M γ CodeInv hCodeInv) mapPtr m bm u ∗
        M.Heap γ (lc0 + hbMapCost (HbAlloc.ofMallocng M γ CodeInv hCodeInv) bm)
                 (blk0 + tableAllocBlocks bm) s ∗
        (muslErrnoAddr s ↦₃₂ e0) ∗
        stackAt s.sp (176 + MallocngStackBytes)) ∗ (F ∗ R)))
    (hnext : ∀ (sf : State) (bm' : BitVec 64) (e1 : BitVec 32),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf → Rust.AllocStatePreserved s sf →
      (ValidNextMask m bm bm' ∧ (bm' ≠ bm → bucketMaskToCapacity bm ≤ u)) →
      SepWP P target_pc sf
        ((U64MapRep pl (HbAlloc.ofMallocng M γ CodeInv hCodeInv) mapPtr (cliMapInsert k v m) bm' (u + 1) ∗
          M.Heap γ (lc0 + hbMapCost (HbAlloc.ofMallocng M γ CodeInv hCodeInv) bm')
                   (blk0 + tableAllocBlocks bm') sf ∗
          (muslErrnoAddr sf ↦₃₂ e1) ∗
          stackAt s.sp (176 + MallocngStackBytes)) ∗ F) post) :
    SepWP P target_pc s Pre post := by
  let A := HbAlloc.ofMallocng M γ CodeInv hCodeInv
  have hstk_le : A.stackBytes + 176 ≤ 2 ^ 64 := show 4096 + 176 ≤ 2 ^ 64 by decide
  refine SepWP.call_subroutine_frame hok
    (x := (mapPtr, m, bm, u, k, v, lc0 + hbMapCost A bm, blk0 + tableAllocBlocks bm)) (F := F)
    hpc hrun hsp_al hlr ?_ (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_
    (fun _ _ _ h => False.elim <| not_satisfies_false_sepConj (by
      dsimp [withCodeInv, hashbrownInsertInfallibleSpec, HbAlloc.ofMallocng] at h; exact h))
  · intro R hm; dsimp only [withCodeInv, hashbrownInsertInfallibleSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hci, ?_⟩; rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hstk_le, hcan⟩, ?_⟩
    have hm1 := hpre R hm
    refine Satisfies.mono (sepConj_mono_left ?_) hm1
    have hh0 : A.Heap (lc0 + hbMapCost A bm) (blk0 + tableAllocBlocks bm) s =
        M.Heap γ (lc0 + hbMapCost A bm) (blk0 + tableAllocBlocks bm) s ∗
        (∃∗ e : BitVec 32, muslErrnoAddr s ↦₃₂ e) := rfl
    have hs0 : A.stackBytes = MallocngStackBytes := rfl
    rw [hh0, hs0]
    exact Entails.trans (by sep_entail)
      (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right (Entails.sepExists_right e0 (Entails.refl _)))))
  · intro sf hpc_f hrun_f hsp_f hcs_f; dsimp only [withCodeInv, hashbrownInsertInfallibleSpec]
    rw [sepConj_assoc]; apply SepWP.pure_elim; rintro ⟨_, halloc⟩
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_left; intro bm'
    conv => arg 4; simp only [sepConj_assoc]; rw [sepConj_left_comm]
    apply SepWP.pure_elim; intro hvmask
    have hh1 : A.Heap ((lc0 + hbMapCost A bm + hbMapCost A bm') - hbMapCost A bm)
        ((blk0 + tableAllocBlocks bm + tableAllocBlocks bm') - tableAllocBlocks bm) sf =
        M.Heap γ (lc0 + hbMapCost A bm') (blk0 + tableAllocBlocks bm') sf ∗
        (∃∗ e : BitVec 32, muslErrnoAddr sf ↦₃₂ e) := by
      rw [add_mid_sub_cancel, add_mid_sub_cancel]; rfl
    have hs0 : A.stackBytes = MallocngStackBytes := rfl
    rw [hh1, hs0]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_left; intro e1
    exact SepWP.weaken_pre (by sep_frame) (hnext sf bm' e1 hpc_f hrun_f hsp_f hcs_f halloc hvmask)

theorem call_hbContainsKey {P : Program} {pl : Obj.Placement} {A : HbAlloc}
    {entry target_pc ret_pc mapPtr bm k : BitVec 64} {m : Map64} {u : Nat} {s : State} {Pre F : SepProp}
    {post : State → SepProp → Prop}
    (hok : subroutine_ok P entry (withCodeInv A (hashbrownContainsKeySpec pl A)))
    (hci : A.CodeInv s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_al : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx0 : s.readReg64 .x0 = mapPtr) (hx1 : s.readReg64 .x1 = k)
    (hpre : ∀ R, (s.mem ⊨ Pre ∗ R) → (s.mem ⊨ U64MapRep pl A mapPtr m bm u ∗ (F ∗ R)))
    (hnext : ∀ sf, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = (if (cliMapLookup k m).isSome then 1#64 else 0#64) →
      StdStatePreserved s sf → s.mem.KeepsFrozen sf.mem →
      SepWP P target_pc sf (U64MapRep pl A mapPtr m bm u ∗ F) post) :
    SepWP P target_pc s Pre post := by
  refine SepWP.call_subroutine_frame hok (x := (mapPtr, m, bm, u, k)) (F := F)
    hpc hrun hsp_al hlr ?_ (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_ (by wp_close_oom_default)
  · intro R hm; dsimp only [withCodeInv, hashbrownContainsKeySpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hci, ?_⟩; rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1⟩, hpre R hm⟩
  · intro sf hpc_f hrun_f hsp_f hcs_f; dsimp only [withCodeInv, hashbrownContainsKeySpec]
    rw [sepConj_assoc]; apply SepWP.pure_elim; rintro ⟨hres, hstd, hfz⟩
    exact hnext sf hpc_f hrun_f hsp_f hcs_f hres hstd hfz

theorem call_hbLen {P : Program} {pl : Obj.Placement} {A : HbAlloc}
    {entry target_pc ret_pc mapPtr bm : BitVec 64} {m : Map64} {u : Nat} {s : State} {Pre F : SepProp}
    {post : State → SepProp → Prop}
    (hok : subroutine_ok P entry (withCodeInv A (hashbrownLenSpec pl A)))
    (hci : A.CodeInv s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_al : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (hx0 : s.readReg64 .x0 = mapPtr)
    (hpre : ∀ R, (s.mem ⊨ Pre ∗ R) → (s.mem ⊨ U64MapRep pl A mapPtr m bm u ∗ (F ∗ R)))
    (hnext : ∀ sf, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf → sf.readReg64 .x0 = BitVec.ofNat 64 m.length →
      StdStatePreserved s sf → s.mem.KeepsFrozen sf.mem →
      SepWP P target_pc sf (U64MapRep pl A mapPtr m bm u ∗ F) post) :
    SepWP P target_pc s Pre post := by
  refine SepWP.call_subroutine_frame hok (x := (mapPtr, m, bm, u)) (F := F)
    hpc hrun hsp_al hlr ?_ (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_ (by wp_close_oom_default)
  · intro R hm; dsimp only [withCodeInv, hashbrownLenSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hci, ?_⟩; rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hx0, hpre R hm⟩
  · intro sf hpc_f hrun_f hsp_f hcs_f; dsimp only [withCodeInv, hashbrownLenSpec]
    rw [sepConj_assoc]; apply SepWP.pure_elim; rintro ⟨hres, hstd, hfz⟩
    exact hnext sf hpc_f hrun_f hsp_f hcs_f hres hstd hfz

theorem call_hbIsEmpty {P : Program} {pl : Obj.Placement} {A : HbAlloc}
    {entry target_pc ret_pc mapPtr bm : BitVec 64} {m : Map64} {u : Nat} {s : State} {Pre F : SepProp}
    {post : State → SepProp → Prop}
    (hok : subroutine_ok P entry (withCodeInv A (hashbrownIsEmptySpec pl A)))
    (hci : A.CodeInv s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_al : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (hx0 : s.readReg64 .x0 = mapPtr)
    (hpre : ∀ R, (s.mem ⊨ Pre ∗ R) → (s.mem ⊨ U64MapRep pl A mapPtr m bm u ∗ (F ∗ R)))
    (hnext : ∀ sf, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf → sf.readReg64 .x0 = (if m.isEmpty then 1#64 else 0#64) →
      StdStatePreserved s sf → s.mem.KeepsFrozen sf.mem →
      SepWP P target_pc sf (U64MapRep pl A mapPtr m bm u ∗ F) post) :
    SepWP P target_pc s Pre post := by
  refine SepWP.call_subroutine_frame hok (x := (mapPtr, m, bm, u)) (F := F)
    hpc hrun hsp_al hlr ?_ (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_ (by wp_close_oom_default)
  · intro R hm; dsimp only [withCodeInv, hashbrownIsEmptySpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hci, ?_⟩; rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hx0, hpre R hm⟩
  · intro sf hpc_f hrun_f hsp_f hcs_f; dsimp only [withCodeInv, hashbrownIsEmptySpec]
    rw [sepConj_assoc]; apply SepWP.pure_elim; rintro ⟨hres, hstd, hfz⟩
    exact hnext sf hpc_f hrun_f hsp_f hcs_f hres hstd hfz

theorem call_hbClear {P : Program} {pl : Obj.Placement} {A : HbAlloc}
    {entry target_pc ret_pc mapPtr bm : BitVec 64} {m : Map64} {u : Nat} {s : State} {Pre F : SepProp}
    {post : State → SepProp → Prop}
    (hok : subroutine_ok P entry (withCodeInv A (hashbrownClearSpec pl A)))
    (hci : A.CodeInv s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_al : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (hx0 : s.readReg64 .x0 = mapPtr)
    (hpre : ∀ R, (s.mem ⊨ Pre ∗ R) →
      (s.mem ⊨ (U64MapRep pl A mapPtr m bm u ∗ stackAt s.sp 32) ∗ (F ∗ R)))
    (hnext : ∀ sf, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf → StdStatePreserved s sf → s.mem.KeepsFrozen sf.mem →
      SepWP P target_pc sf ((U64MapRep pl A mapPtr [] bm u ∗ stackAt s.sp 32) ∗ F) post) :
    SepWP P target_pc s Pre post := by
  refine SepWP.call_subroutine_frame hok (x := (mapPtr, m, bm, u)) (F := F)
    hpc hrun hsp_al hlr ?_ (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_ (by wp_close_oom_default)
  · intro R hm; dsimp only [withCodeInv, hashbrownClearSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hci, ?_⟩; rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hx0, hpre R hm⟩
  · intro sf hpc_f hrun_f hsp_f hcs_f; dsimp only [withCodeInv, hashbrownClearSpec]
    rw [sepConj_assoc]; apply SepWP.pure_elim; rintro ⟨hstd, hfz⟩
    exact hnext sf hpc_f hrun_f hsp_f hcs_f hstd hfz

theorem call_hbWithCapacityInf {P : Program} {pl : Obj.Placement} {addrs : MallocngAddrs} {lim : MallocngLimits}
    (M : MallocngCoreIface P addrs lim) (γ : GhostName)
    (CodeInv : Memory → Prop)
    (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    {entry target_pc ret_pc mapPtr cap : BitVec 64} {lc0 blk0 : Nat} {e0 : BitVec 32}
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop}
    (hok : subroutine_ok P entry
      (withCodeInv (HbAlloc.ofMallocng M γ CodeInv hCodeInv)
        (hashbrownWithCapacityInfallibleSpec pl (HbAlloc.ofMallocng M γ CodeInv hCodeInv))))
    (hci : CodeInv s.mem) (hal : mapPtr.toNat % 8 = 0) (hfit : mapPtr.toNat + 32 ≤ 2 ^ 64)
    (hcan : HbCanWithCapacity (HbAlloc.ofMallocng M γ CodeInv hCodeInv) cap lc0 blk0)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_al : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx0 : s.readReg64 .x0 = cap) (hx8 : s.readReg64 .x8 = mapPtr)
    (hpre : ∀ R, (s.mem ⊨ Pre ∗ R) →
      (s.mem ⊨ (hbRodata pl ∗ memRegion mapPtr 32 ∗ M.Heap γ lc0 blk0 s ∗
        (muslErrnoAddr s ↦₃₂ e0) ∗ stackAt s.sp (80 + MallocngStackBytes)) ∗ (F ∗ R)))
    (hnext : ∀ (sf : State) (e1 : BitVec 32),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf → Rust.AllocStatePreserved s sf →
      let bm := capToBucketMask cap.toNat
      SepWP P target_pc sf
        ((U64MapRep pl (HbAlloc.ofMallocng M γ CodeInv hCodeInv) mapPtr [] bm 0 ∗
          hbRodata pl ∗
          M.Heap γ (lc0 + hbMapCost (HbAlloc.ofMallocng M γ CodeInv hCodeInv) bm)
                   (blk0 + tableAllocBlocks bm) sf ∗
          (muslErrnoAddr sf ↦₃₂ e1) ∗
          stackAt s.sp (80 + MallocngStackBytes)) ∗ F) post) :
    SepWP P target_pc s Pre post := by
  let A := HbAlloc.ofMallocng M γ CodeInv hCodeInv
  have hstk_le : A.stackBytes + 80 ≤ 2 ^ 64 := show 4096 + 80 ≤ 2 ^ 64 by decide
  refine SepWP.call_subroutine_frame hok (x := (mapPtr, cap, lc0, blk0)) (F := F)
    hpc hrun hsp_al hlr ?_ (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_
    (fun _ _ _ h => False.elim <| not_satisfies_false_sepConj (by
      dsimp [withCodeInv, hashbrownWithCapacityInfallibleSpec, HbAlloc.ofMallocng] at h; exact h))
  · intro R hm; dsimp only [withCodeInv, hashbrownWithCapacityInfallibleSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hci, ?_⟩; rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hal, hfit, hstk_le, hcan⟩, ?_⟩
    have hm1 := hpre R hm
    refine Satisfies.mono (sepConj_mono_left ?_) hm1
    have hh0 : A.Heap lc0 blk0 s = M.Heap γ lc0 blk0 s ∗ (∃∗ e : BitVec 32, muslErrnoAddr s ↦₃₂ e) := rfl
    have hs0 : A.stackBytes = MallocngStackBytes := rfl
    rw [hh0, hs0]
    exact Entails.trans (by sep_entail)
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
        (sepConj_mono_right (Entails.sepExists_right e0 (Entails.refl _))))))
  · intro sf hpc_f hrun_f hsp_f hcs_f; dsimp only [withCodeInv, hashbrownWithCapacityInfallibleSpec]
    rw [sepConj_assoc]; apply SepWP.pure_elim; intro halloc
    let bm := capToBucketMask cap.toNat
    have hh1 : A.Heap (lc0 + hbMapCost A bm) (blk0 + tableAllocBlocks bm) sf =
        M.Heap γ (lc0 + hbMapCost A bm) (blk0 + tableAllocBlocks bm) sf ∗
        (∃∗ e : BitVec 32, muslErrnoAddr sf ↦₃₂ e) := rfl
    have hs0 : A.stackBytes = MallocngStackBytes := rfl
    rw [hh1, hs0]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_left; intro e1
    exact SepWP.weaken_pre (by sep_frame) (hnext sf e1 hpc_f hrun_f hsp_f hcs_f halloc)

theorem call_hbDrop {P : Program} {pl : Obj.Placement} {addrs : MallocngAddrs} {lim : MallocngLimits}
    (M : MallocngCoreIface P addrs lim) (γ : GhostName)
    (CodeInv : Memory → Prop)
    (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    {entry target_pc ret_pc mapPtr bm : BitVec 64} {m : Map64} {u lc0 blk0 : Nat} {e0 : BitVec 32}
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop}
    (hok : subroutine_ok P entry
      (withCodeInv (HbAlloc.ofMallocng M γ CodeInv hCodeInv)
        (hashbrownDropSpec pl (HbAlloc.ofMallocng M γ CodeInv hCodeInv))))
    (hci : CodeInv s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_al : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (hx0 : s.readReg64 .x0 = mapPtr)
    (hpre : ∀ R, (s.mem ⊨ Pre ∗ R) →
      (s.mem ⊨ (U64MapRep pl (HbAlloc.ofMallocng M γ CodeInv hCodeInv) mapPtr m bm u ∗
        M.Heap γ (lc0 + hbMapCost (HbAlloc.ofMallocng M γ CodeInv hCodeInv) bm)
                 (blk0 + tableAllocBlocks bm) s ∗
        (muslErrnoAddr s ↦₃₂ e0) ∗
        stackAt s.sp MallocngStackBytes) ∗ (F ∗ R)))
    (hnext : ∀ (sf : State) (e1 : BitVec 32),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf → Rust.AllocStatePreserved s sf →
      SepWP P target_pc sf
        ((memRegion mapPtr 32 ∗ hbRodata pl ∗ M.Heap γ lc0 blk0 sf ∗
          (muslErrnoAddr sf ↦₃₂ e1) ∗ stackAt s.sp MallocngStackBytes) ∗ F) post) :
    SepWP P target_pc s Pre post := by
  let A := HbAlloc.ofMallocng M γ CodeInv hCodeInv
  refine SepWP.call_subroutine_frame hok
    (x := (mapPtr, m, bm, u, lc0 + hbMapCost A bm, blk0 + tableAllocBlocks bm)) (F := F)
    hpc hrun hsp_al hlr ?_ (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_ (by wp_close_oom_default)
  · intro R hm; dsimp only [withCodeInv, hashbrownDropSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hci, ?_⟩; rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hx0, ?_⟩
    have hm1 := hpre R hm
    refine Satisfies.mono (sepConj_mono_left ?_) hm1
    have hh0 : A.Heap (lc0 + hbMapCost A bm) (blk0 + tableAllocBlocks bm) s =
        M.Heap γ (lc0 + hbMapCost A bm) (blk0 + tableAllocBlocks bm) s ∗
        (∃∗ e : BitVec 32, muslErrnoAddr s ↦₃₂ e) := rfl
    have hs0 : A.stackBytes = MallocngStackBytes := rfl
    rw [hh0, hs0]
    exact Entails.trans (by sep_entail)
      (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right (Entails.sepExists_right e0 (Entails.refl _)))))
  · intro sf hpc_f hrun_f hsp_f hcs_f; dsimp only [withCodeInv, hashbrownDropSpec]
    rw [sepConj_assoc]; apply SepWP.pure_elim; intro halloc
    have hh1 : A.Heap ((lc0 + hbMapCost A bm) - hbMapCost A bm)
        ((blk0 + tableAllocBlocks bm) - tableAllocBlocks bm) sf =
        M.Heap γ lc0 blk0 sf ∗ (∃∗ e : BitVec 32, muslErrnoAddr sf ↦₃₂ e) := by
      rw [Nat.add_sub_cancel, Nat.add_sub_cancel]; rfl
    have hs0 : A.stackBytes = MallocngStackBytes := rfl
    rw [hh1, hs0]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_left; intro e1
    exact SepWP.weaken_pre (by sep_frame) (hnext sf e1 hpc_f hrun_f hsp_f hcs_f halloc)

theorem call_hbFree {P : Program} {addrs : MallocngAddrs} {lim : MallocngLimits}
    (M : MallocngCoreIface P addrs lim) (γ : GhostName)
    {target_pc ret_pc p : BitVec 64} {lc blk req : Nat} {e0 : BitVec 32}
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop}
    (hp_nz : p ≠ 0#64)
    (hpc : s.pc = addrs.freeAddr) (hrun : s.status = .Running) (hsp_al : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (hx0 : s.readReg64 .x0 = p)
    (hpre : ∀ R, (s.mem ⊨ Pre ∗ R) →
      (s.mem ⊨ (M.Heap γ lc blk s ∗ M.Block γ p req ∗ memRegion p req ∗
        (muslErrnoAddr s ↦₃₂ e0) ∗ stackAt s.sp MallocngStackBytes) ∗ (F ∗ R)))
    (hnext : ∀ (sf : State) (e1 : BitVec 32),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf → MallocngStatePreserved s sf →
      SepWP P target_pc sf
        ((M.Heap γ (lc - mallocngBlockCost req) (blk - 1) sf ∗
          (muslErrnoAddr sf ↦₃₂ e1) ∗ stackAt s.sp MallocngStackBytes) ∗ F) post) :
    SepWP P target_pc s Pre post := by
  refine SepWP.call_subroutine_frame (M.free_ok γ) (x := (lc, blk, some req, e0)) (F := F)
    hpc hrun hsp_al hlr ?_ (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_ (by wp_close_oom_default)
  · intro R hm; dsimp only; rw [show s.readReg64 (.gpr 0#5) = p from hx0]
    exact Satisfies.mono (sepConj_mono_left <| by
      rw [pure_sepConj_of_true hp_nz]; sep_entail) (hpre R hm)
  · intro sf hpc_f hrun_f hsp_f hcs_f; dsimp only
    rw [sepConj_assoc]; apply SepWP.pure_elim; intro hmsp
    have herr : muslErrnoAddr s = muslErrnoAddr sf := by simp [muslErrnoAddr, hmsp.2.2.2.1]
    rw [herr]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_left; intro e1
    exact SepWP.weaken_pre (by sep_frame) (hnext sf e1 hpc_f hrun_f hsp_f hcs_f hmsp)

/-! ## Pure-CPU parsers and newline scanner -/

def PureCpuStep (s0 sf : State) : Prop :=
  sf.sp = s0.sp ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧
  CpuAuxPreserved s0 sf ∧ CalleeSavedPreserved s0 sf

theorem PureCpuStep.refl (s : State) : PureCpuStep s s :=
  ⟨rfl, rfl, rfl, CpuAuxPreserved.refl s, CalleeSavedPreserved.rfl s⟩

theorem PureCpuStep.trans {s0 s1 s2 : State}
    (h01 : PureCpuStep s0 s1) (h12 : PureCpuStep s1 s2) : PureCpuStep s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h01.2.2.2.1.trans h12.2.2.2.1, h01.2.2.2.2.trans h12.2.2.2.2⟩

local macro "close_cpu_step " s:term : term =>
  `(⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
     by simp [wp_norm, arm64_norm], by simp [CpuAuxPreserved.refl $s], by close_cs⟩)

theorem ze32_beq_byte (b c : BitVec 8) :
    (b.zeroExtend 32 == c.zeroExtend 32) = (b == c) := by
  by_cases h : b = c
  · subst h; simp
  · have h32 : b.zeroExtend 32 ≠ c.zeroExtend 32 := fun he => by
      have ht := congrArg BitVec.toNat he
      rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth,
          Nat.mod_eq_of_lt (by have := b.isLt; omega),
          Nat.mod_eq_of_lt (by have := c.isLt; omega)] at ht
      exact h (BitVec.eq_of_toNat_eq ht)
    simp [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr h32]

theorem ofNat64_ult_const {n k : Nat} (hn : n < 2 ^ 64) (hk : k < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 n) (BitVec.ofNat 64 k) = decide (n < k) := by
  rw [BitVec.ult, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hk]

theorem ofNat64_ule_const {k n : Nat} (hk : k < 2 ^ 64) (hn : n < 2 ^ 64) :
    BitVec.ule (BitVec.ofNat 64 k) (BitVec.ofNat 64 n) = decide (k ≤ n) := by
  rw [BitVec.ule, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hn]

theorem mvn_add_of_lt {k n : Nat} (hk : k < n) (hn : n < 2 ^ 64) :
    ~~~(BitVec.ofNat 64 k) + BitVec.ofNat 64 n = BitVec.ofNat 64 (n - (k + 1)) := by
  have hk2 : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hn2 : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have hd2 : (BitVec.ofNat 64 (n - (k + 1))).toNat = n - (k + 1) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_not, hk2, hn2, hd2,
      show 2 ^ 64 - 1 - k + n = 2 ^ 64 + (n - (k + 1)) by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

private theorem bytesEq_loop_wp {Q : Program} {C : HbCliLayout} {target ret_pc ptr1 ptr2 : BitVec 64}
    {bs1 bs2 : List (BitVec 8)} {s0 : State} {F : SepProp} {post : State → SepProp → Prop}
    (hc : Q.hasCode C.bytesEqAddr hbBytesEqWords)
    (hseq : bs1.length = bs2.length) (hlen : bs1.length < 2 ^ 64)
    (hpc : s0.pc = C.bytesEqAddr + 0x08#64) (hrun : s0.status = .Running)
    (hlr : s0.readReg64 Reg.lr = ret_pc)
    (hx0 : s0.readReg64 .x0 = ptr1) (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 bs1.length)
    (hx2 : s0.readReg64 .x2 = ptr2)
    (hNext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → PureCpuStep s0 sf →
      sf.readReg64 .x0 = (if (bs1 == bs2) = true then 1#64 else 0#64) →
      SepWP Q target sf ((ptr1 ↦ₛ bs1) ∗ (ptr2 ↦ᵣ bs2) ∗ F) post) :
    SepWP Q target s0 ((ptr1 ↦ₛ bs1) ∗ (ptr2 ↦ᵣ bs2) ∗ F) post := by
  induction bs1 generalizing bs2 ptr1 ptr2 s0 F with
  | nil =>
    rcases bs2 with _ | ⟨_, _⟩
    · have hx1_0 : s0.readReg64 .x1 = 0#64 := hx1
      wp_steps 5
      exact hNext _ wp_a (by simp [wp_norm, arm64_norm, hrun]) (close_cpu_step s0)
        (by simp (config := { decide := true }) [wp_norm, arm64_norm])
    · simp at hseq
  | cons c1 r1 ih =>
    rcases bs2 with _ | ⟨c2, r2⟩
    · simp at hseq
    · have hnz : (BitVec.ofNat 64 (c1 :: r1).length == 0#64) = false := by
        rw [beq_eq_false_iff_ne]; intro he; have ht := congrArg BitVec.toNat he
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen] at ht; simp at ht
      have hsub : BitVec.ofNat 64 (c1 :: r1).length - 1#64 = BitVec.ofNat 64 r1.length := by
        rw [List.length_cons, BitVec.ofNat_add]; bv_lin
      conv => arg 4; rw [pointsToBytes_cons, pointsToBytesRO_cons]
      wp_steps 7
      have hcond := ze32_beq_byte c1 c2
      by_cases hc_eq : c1 = c2
      · subst hc_eq
        have hseq' : r1.length = r2.length := by simp at hseq; exact hseq
        have hbeq : (c1.zeroExtend 32 == c1.zeroExtend 32) = true := by simp
        wp_steps 1
        exact SepWP.weaken_pre (by sep_frame) (ih (bs2 := r2) (ptr1 := ptr1 + 1#64)
          (ptr2 := ptr2 + 1#64) (F := (ptr1 ↦₈ c1) ∗ (ptr2 ↦₈ᵣ c1) ∗ F)
          hseq' (by simp at hlen; omega)
          wp_a (by simp [wp_norm, arm64_norm, hrun]) wp_a wp_a
          (by simp only [wp_norm, arm64_norm, List.length_cons, ← hseq', BitVec.ofNat_add]) wp_a
          (fun sf h1 h2 h3 h4 => SepWP.weaken_pre
            (by rw [pointsToBytes_cons, pointsToBytesRO_cons]; sep_frame)
            (hNext sf h1 h2 (PureCpuStep.trans (close_cpu_step s0) h3)
              (by simpa [bytes_beq_cons_eq r1 r2 rfl] using h4))))
      · have hbeq : (c1.zeroExtend 32 == c2.zeroExtend 32) = false := by
          rw [hcond]; exact beq_eq_false_iff_ne.mpr hc_eq
        wp_steps 3
        conv => arg 4; rw [← pointsToBytes_cons, ← pointsToBytesRO_cons]
        exact hNext _ wp_a (by simp [wp_norm, arm64_norm, hrun]) (close_cpu_step s0)
          (by simp (config := { decide := true }) [wp_norm, arm64_norm,
               bytes_beq_cons_ne r1 r2 hc_eq])

theorem hbBytesEq_wp {Q : Program} {C : HbCliLayout} {target ret_pc ptr1 ptr2 : BitVec 64}
    {bs1 bs2 : List (BitVec 8)} {s0 : State} {F : SepProp} {post : State → SepProp → Prop}
    (hc : CodeChunks Q (hbBytesEqChunks C))
    (hlen1 : bs1.length < 2 ^ 64) (hlen2 : bs2.length < 2 ^ 64)
    (hpc : s0.pc = C.bytesEqAddr) (hrun : s0.status = .Running)
    (hlr : s0.readReg64 Reg.lr = ret_pc)
    (hx0 : s0.readReg64 .x0 = ptr1) (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 bs1.length)
    (hx2 : s0.readReg64 .x2 = ptr2) (hx3 : s0.readReg64 .x3 = BitVec.ofNat 64 bs2.length)
    (hNext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → PureCpuStep s0 sf →
      sf.readReg64 .x0 = (if (bs1 == bs2) = true then 1#64 else 0#64) →
      SepWP Q target sf ((ptr1 ↦ₛ bs1) ∗ (ptr2 ↦ᵣ bs2) ∗ F) post) :
    SepWP Q target s0 ((ptr1 ↦ₛ bs1) ∗ (ptr2 ↦ᵣ bs2) ∗ F) post := by
  have hc0 : Q.hasCode C.bytesEqAddr hbBytesEqWords := hc
  by_cases hseq : bs1.length = bs2.length
  · have hbne : (BitVec.ofNat 64 bs1.length != BitVec.ofNat 64 bs2.length) = false := by
      rw [hseq]; simp
    wp_steps 2
    exact bytesEq_loop_wp hc0 hseq hlen1 wp_a (by simp [wp_norm, arm64_norm, hrun])
      wp_a wp_a (by simp [wp_norm, arm64_norm, hx1]) wp_a
      (fun sf h1 h2 h3 h4 => hNext sf h1 h2 (PureCpuStep.trans (close_cpu_step s0) h3) h4)
  · have hbne : (BitVec.ofNat 64 bs1.length != BitVec.ofNat 64 bs2.length) = true := by
      rw [bne_iff_ne]; intro he; have ht := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen1, Nat.mod_eq_of_lt hlen2] at ht
      exact hseq ht
    wp_steps 5
    exact hNext _ wp_a (by simp [wp_norm, arm64_norm, hrun]) (close_cpu_step s0)
      (by simp (config := { decide := true }) [wp_norm, arm64_norm, bytes_beq_false_of_length_ne hseq])

local macro "unpack_cmd_code " chunks:ident h:term : tactic => `(tactic| (
  have _hc := stdoutToStepFacts $h
  simp only [$chunks:ident, stdoutStepFacts, stdoutStepAcc, fetchAtAcc',
    Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at _hc
  (repeat obtain ⟨_, _hc⟩ := _hc); try clear _hc))

local macro "norm_jmp" : tactic =>
  `(tactic| conv in State.setPC _ _ => arg 2; rw [bv64_add_sub_cancel'])

local macro "unpack_cells " k:num : tactic => `(tactic| (
  try simp only [Nat.reduceMul]
  cells_unfold
  try simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  iterate $k (apply SepWP.exists_left; intro _)))

local macro "repack_cells" : tactic => `(tactic| (
  try simp only [Nat.reduceMul]
  cells_unfold
  try simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  sep_entail))

local macro "unpack_cs " h:ident : tactic =>
  `(tactic| obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩ := $h)

theorem hbStripPrefix_wp {Q : Program} {C : HbCliLayout}
    {target ret_pc sp0 linePtr pfxPtr : BitVec 64}
    {line pfx : List (BitVec 8)} {s0 : State} {F : SepProp} {post : State → SepProp → Prop}
    (hcS : CodeChunks Q (hbStripPrefixChunks C)) (hcB : CodeChunks Q (hbBytesEqChunks C))
    (hptr_nz : linePtr ≠ 0#64) (hptr_fit : linePtr.toNat + line.length < 2 ^ 64)
    (hpfx_len : pfx.length < 2 ^ 64)
    (hpc : s0.pc = C.stripPrefixAddr) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0) (hsp_al : s0.spAligned = true)
    (hlr : s0.readReg64 Reg.lr = ret_pc)
    (hx0 : s0.readReg64 .x0 = linePtr) (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 line.length)
    (hx2 : s0.readReg64 .x2 = pfxPtr) (hx3 : s0.readReg64 .x3 = BitVec.ofNat 64 pfx.length)
    (hSome : ∀ (sf : State) (rest : List (BitVec 8)),
      stripBytePrefix pfx line = some rest →
      sf.pc = ret_pc → sf.status = .Running → PureCpuStep s0 sf →
      sf.readReg64 .x0 = linePtr + BitVec.ofNat 64 pfx.length →
      linePtr + BitVec.ofNat 64 pfx.length ≠ 0#64 →
      sf.readReg64 .x1 = BitVec.ofNat 64 rest.length →
      SepWP Q target sf ((linePtr ↦ₛ line) ∗ (pfxPtr ↦ᵣ pfx) ∗ stackAt sp0 48 ∗ F) post)
    (hNone : ∀ sf : State,
      stripBytePrefix pfx line = none →
      sf.pc = ret_pc → sf.status = .Running → PureCpuStep s0 sf →
      sf.readReg64 .x0 = 0#64 →
      SepWP Q target sf ((linePtr ↦ₛ line) ∗ (pfxPtr ↦ᵣ pfx) ∗ stackAt sp0 48 ∗ F) post) :
    SepWP Q target s0 ((linePtr ↦ₛ line) ∗ (pfxPtr ↦ᵣ pfx) ∗ stackAt sp0 48 ∗ F) post := by
  subst hsp
  have hline_len : line.length < 2 ^ 64 := by omega
  unpack_cmd_code hbStripPrefixChunks hcS
  conv => arg 4; rw [show (48 : Nat) = 8 * 6 from rfl, stackAt_eq_cells s0.sp 6]
  unpack_cells 6
  wp_steps 5
  have hult := ofNat64_ult_const hline_len hpfx_len
  have hule := ofNat64_ule_const hpfx_len hline_len
  by_cases hlt : line.length < pfx.length
  · have hult_t : BitVec.ult (BitVec.ofNat 64 line.length) (BitVec.ofNat 64 pfx.length) = true := by
      rw [hult]; exact decide_eq_true hlt
    have hule_f : BitVec.ule (BitVec.ofNat 64 pfx.length) (BitVec.ofNat 64 line.length) = false := by
      rw [hule]; exact decide_eq_false (by omega)
    wp_steps 7
    refine SepWP.weaken_pre_frame (fun _ _ => by
        rw [show (48 : Nat) = 8 * 6 from rfl, stackAt_eq_cells s0.sp 6]; repack_cells)
      (hNone _ (stripBytePrefix_eq_none_of_lt hlt) wp_a
        (by simp [wp_norm, arm64_norm, hrun]) (close_cpu_step s0) wp_a)
  · have hle : pfx.length ≤ line.length := by omega
    have hult_f : BitVec.ult (BitVec.ofNat 64 line.length) (BitVec.ofNat 64 pfx.length) = false := by
      rw [hult]; exact decide_eq_false hlt
    have hule_t : BitVec.ule (BitVec.ofNat 64 pfx.length) (BitVec.ofNat 64 line.length) = true := by
      rw [hule]; exact decide_eq_true hle
    wp_steps 5; norm_jmp
    have htake_len : (line.take pfx.length).length = pfx.length := List.length_take_of_le hle
    conv => arg 4; rw [pointsToBytes_take_drop linePtr pfx.length line hle]
    refine SepWP.weaken_pre (by sep_frame)
      (hbBytesEq_wp hcB (bs1 := line.take pfx.length) (bs2 := pfx)
        (ret_pc := C.stripPrefixAddr + 0x28#64)
        (by rw [htake_len]; exact hpfx_len) hpfx_len wp_a (by simp [wp_norm, arm64_norm, hrun])
        wp_a wp_a (by simp [wp_norm, arm64_norm, htake_len]) wp_a wp_a
        fun s1 hpc1 hrun1 hp1 hx0_1 => ?_)
    obtain ⟨hsp1, hfs1, htr1, haux1, hcs1⟩ := hp1
    have hsp1_eq : s1.sp = s0.sp - 48#64 := hsp1.trans (by simp [wp_norm, arm64_norm])
    have hx19_1 : s1.readReg64 (.gpr 19#5) = BitVec.ofNat 64 (line.drop pfx.length).length := by
      rw [← Reg.x19, hcs1.readReg64_x19]
      simp only [wp_norm, arm64_norm, List.length_drop]
      have hl1 : line.length = (line.length - pfx.length) + pfx.length := by omega
      conv => lhs; arg 1; rw [hl1, BitVec.ofNat_add]
      bv_lin
    have hx20_1 : s1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 pfx.length := by
      rw [← Reg.x20, hcs1.readReg64_x20]; simp [wp_norm, arm64_norm]
    have hx21_1 : s1.readReg64 (.gpr 21#5) = linePtr := by
      rw [← Reg.x21, hcs1.readReg64_x21]; simp [wp_norm, arm64_norm]
    unpack_cs hcs1
    by_cases heq : (line.take pfx.length == pfx) = true
    · simp only [heq, ↓reduceIte] at hx0_1
      have hx0_1' : s1.readReg64 (.gpr 0#5) = 1#64 := hx0_1
      have hres_nz : linePtr + BitVec.ofNat 64 pfx.length ≠ 0#64 := fun hz => by
        have ht := congrArg BitVec.toNat hz
        have hpz : 0 < linePtr.toNat :=
          Nat.pos_of_ne_zero fun h0 => hptr_nz (BitVec.eq_of_toNat_eq h0)
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpfx_len,
            Nat.mod_eq_of_lt (by omega)] at ht
        simp only [BitVec.toNat_ofNat, Nat.zero_mod] at ht; omega
      wp_steps 8
      refine SepWP.weaken_pre_frame (fun _ _ => by
          rw [pointsToBytes_take_drop linePtr pfx.length line hle,
              show (48 : Nat) = 8 * 6 from rfl, stackAt_eq_cells s0.sp 6]; repack_cells)
        (hSome _ (line.drop pfx.length) (stripBytePrefix_eq_some_of_take_eq hle (beq_iff_eq.mp heq))
          wp_a (by simp [wp_norm, arm64_norm, hrun1])
          ⟨by simp [wp_norm, arm64_norm],
           by simp [wp_norm, arm64_norm, hfs1],
           by simp [wp_norm, arm64_norm, htr1],
           (by simp [CpuAuxPreserved.refl s0] : CpuAuxPreserved s0 _).trans
             (haux1.trans (by simp [CpuAuxPreserved.refl s1])),
           by close_cs⟩
          wp_a hres_nz wp_a)
    · simp only [heq, Bool.false_eq_true, ↓reduceIte] at hx0_1
      have hx0_1' : s1.readReg64 (.gpr 0#5) = 0#64 := hx0_1
      wp_steps 7
      refine SepWP.weaken_pre_frame (fun _ _ => by
          rw [pointsToBytes_take_drop linePtr pfx.length line hle,
              show (48 : Nat) = 8 * 6 from rfl, stackAt_eq_cells s0.sp 6]; repack_cells)
        (hNone _ (stripBytePrefix_eq_none_of_take_ne (beq_eq_false_iff_ne.mp (Bool.eq_false_iff.mpr heq)))
          wp_a (by simp [wp_norm, arm64_norm, hrun1])
          ⟨by simp [wp_norm, arm64_norm],
           by simp [wp_norm, arm64_norm, hfs1],
           by simp [wp_norm, arm64_norm, htr1],
           (by simp [CpuAuxPreserved.refl s0] : CpuAuxPreserved s0 _).trans
             (haux1.trans (by simp [CpuAuxPreserved.refl s1])),
           by close_cs⟩
          wp_a)

private theorem splitOnceSpace_loop_wp {Q : Program} {C : HbCliLayout}
    {target ret_pc restPtr outPtr : BitVec 64} {rest : List (BitVec 8)}
    {fuel idx : Nat} {o0 o1 o2 o3 : BitVec 64} {s0 : State} {F : SepProp}
    {post : State → SepProp → Prop}
    (hc : Q.hasCode C.splitOnceSpaceAddr hbSplitOnceSpaceWords)
    (hfuel : rest.length - idx ≤ fuel) (hidx : idx < rest.length) (hlen : rest.length < 2 ^ 64)
    (hprev : ∀ j (hj : j < idx), rest[j]'(by omega) ≠ 0x20#8)
    (hpc : s0.pc = C.splitOnceSpaceAddr + 0x08#64) (hrun : s0.status = .Running)
    (hlr : s0.readReg64 Reg.lr = ret_pc)
    (hx0 : s0.readReg64 .x0 = restPtr) (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 rest.length)
    (hx8 : s0.readReg64 .x8 = outPtr) (hx9 : s0.readReg64 .x9 = BitVec.ofNat 64 idx)
    (hSome : ∀ (sf : State) (k : Nat) (_hk : k < rest.length),
      splitFirstByte 0x20#8 rest = some (rest.take k, rest.drop (k + 1)) →
      sf.pc = ret_pc → sf.status = .Running → PureCpuStep s0 sf →
      SepWP Q target sf
        ((restPtr ↦ₛ rest) ∗ (outPtr ↦₆₄ restPtr) ∗ ((outPtr + 8#64) ↦₆₄ BitVec.ofNat 64 k) ∗
         ((outPtr + 16#64) ↦₆₄ (restPtr + BitVec.ofNat 64 (k + 1))) ∗
         ((outPtr + 24#64) ↦₆₄ BitVec.ofNat 64 (rest.drop (k + 1)).length) ∗ F) post)
    (hNone : ∀ sf : State,
      splitFirstByte 0x20#8 rest = none →
      sf.pc = ret_pc → sf.status = .Running → PureCpuStep s0 sf →
      SepWP Q target sf
        ((restPtr ↦ₛ rest) ∗ (outPtr ↦₆₄ 0#64) ∗ ((outPtr + 8#64) ↦₆₄ o1) ∗
         ((outPtr + 16#64) ↦₆₄ o2) ∗ ((outPtr + 24#64) ↦₆₄ o3) ∗ F) post) :
    SepWP Q target s0
      ((restPtr ↦ₛ rest) ∗ (outPtr ↦₆₄ o0) ∗ ((outPtr + 8#64) ↦₆₄ o1) ∗
       ((outPtr + 16#64) ↦₆₄ o2) ∗ ((outPtr + 24#64) ↦₆₄ o3) ∗ F) post := by
  induction fuel generalizing idx s0 with
  | zero => omega
  | succ fuel ih =>
    have hb_eq : rest.getD idx 0#8 = rest[idx] := by simp [List.getD, hidx]
    conv => arg 4; rw [pointsToBytes_focus8 restPtr rest idx hidx]
    wp_steps 2
    have hcond : (rest[idx].zeroExtend 32 == 0x20#32) = (rest[idx] == 0x20#8) :=
      ze32_beq_byte rest[idx] 0x20#8
    by_cases hsp : rest[idx] = 0x20#8
    · have hbeq : (rest[idx].zeroExtend 32 == 0x20#32) = true := by
        rw [hcond]; exact beq_iff_eq.mpr hsp
      have hule : BitVec.ule (BitVec.ofNat 64 idx) (BitVec.ofNat 64 rest.length) = true := by
        rw [ofNat64_ule_const (by omega) hlen]; exact decide_eq_true (by omega)
      have hult : BitVec.ult (BitVec.ofNat 64 rest.length) (BitVec.ofNat 64 idx) = false := by
        rw [ofNat64_ult_const hlen (by omega)]; exact decide_eq_false (by omega)
      have hbne : (BitVec.ofNat 64 rest.length != BitVec.ofNat 64 idx) = true := by
        rw [bne_iff_ne]; intro he; have ht := congrArg BitVec.toNat he
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen, Nat.mod_eq_of_lt (by omega)] at ht
        omega
      have hmvn : ~~~(BitVec.ofNat 64 idx) + BitVec.ofNat 64 rest.length =
          BitVec.ofNat 64 (rest.drop (idx + 1)).length := by
        rw [mvn_add_of_lt hidx hlen, List.length_drop]
      have hadd1 : restPtr + BitVec.ofNat 64 idx + 1#64 = restPtr + BitVec.ofNat 64 (idx + 1) := by
        rw [BitVec.ofNat_add]; bv_lin
      wp_steps 11
      conv => arg 4; rw [← pointsToBytes_focus8 restPtr rest idx hidx]
      exact SepWP.weaken_pre (by sep_frame)
        (hSome _ idx hidx (splitFirstByte_of_first_eq hidx hsp hprev)
          wp_a (by simp [wp_norm, arm64_norm, hrun]) (close_cpu_step s0))
    · have hbeq : (rest[idx].zeroExtend 32 == 0x20#32) = false := by
        rw [hcond]; exact beq_eq_false_iff_ne.mpr hsp
      have hidx1 : BitVec.ofNat 64 idx + 1#64 = BitVec.ofNat 64 (idx + 1) :=
        (BitVec.ofNat_add idx 1).symm
      wp_steps 3
      by_cases hmore : idx + 1 < rest.length
      · have hbne : (BitVec.ofNat 64 rest.length != BitVec.ofNat 64 (idx + 1)) = true := by
          rw [bne_iff_ne]; intro he; have ht := congrArg BitVec.toNat he
          rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen, Nat.mod_eq_of_lt (by omega)] at ht
          omega
        wp_steps 1
        conv => arg 4; rw [← pointsToBytes_focus8 restPtr rest idx hidx]
        have hprev' : ∀ j (hj : j < idx + 1), rest[j]'(by omega) ≠ 0x20#8 := fun j hj => by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
          · exact hprev j hlt
          · exact hsp
        exact ih (idx := idx + 1) (by omega) hmore hprev'
          wp_a (by simp [wp_norm, arm64_norm, hrun]) wp_a wp_a wp_a wp_a wp_a
          (fun sf k hk h1 h2 h3 h4 => hSome sf k hk h1 h2 h3 (PureCpuStep.trans (close_cpu_step s0) h4))
          (fun sf h1 h2 h3 h4 => hNone sf h1 h2 h3 (PureCpuStep.trans (close_cpu_step s0) h4))
      · have heq_len : idx + 1 = rest.length := by omega
        have hbne : (BitVec.ofNat 64 rest.length != BitVec.ofNat 64 (idx + 1)) = false := by
          rw [heq_len]; simp
        have hall : ∀ j (hj : j < rest.length), rest[j] ≠ 0x20#8 := fun j hj => by
          rcases Nat.lt_succ_iff_lt_or_eq.mp (heq_len ▸ hj) with hlt | rfl
          · exact hprev j hlt
          · exact hsp
        wp_steps 3
        conv => arg 4; rw [← pointsToBytes_focus8 restPtr rest idx hidx]
        exact SepWP.weaken_pre (by sep_frame)
          (hNone _ (splitFirstByte_of_forall_ne hall)
            wp_a (by simp [wp_norm, arm64_norm, hrun]) (close_cpu_step s0))

theorem digit_ult_nine (b : BitVec 8) :
    (9#32).ult (b.zeroExtend 32 - 0x30#32) = !(0x30#8 ≤ b && b ≤ 0x39#8) := by
  have hiff := digitSub_le_nine_iff b
  rw [BitVec.le_def] at hiff
  rw [BitVec.ult, Bool.eq_iff_iff, decide_eq_true_eq, Bool.not_eq_true', Bool.eq_false_iff]
  refine ⟨fun hlt ht => ?_, fun hnf => ?_⟩
  · have hle := hiff.mpr ht; omega
  · by_cases hle : (b.zeroExtend 32 - 0x30#32).toNat ≤ (9#32).toNat
    · exact False.elim (hnf (hiff.mp hle))
    · omega

theorem add_ule_left (x y : BitVec 64) :
    x.ule (x + y) = decide (x.toNat + y.toNat < 2 ^ 64) := by
  have hx := x.isLt; have hy := y.isLt
  rw [BitVec.ule, BitVec.toNat_add, Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
  omega

theorem umulh_beq_zero (acc : BitVec 64) :
    (0#64 == BitVec.truncate 64 ((BitVec.zeroExtend 128 acc * 10#128) >>> 64)) =
      decide ((acc.toNat * 10) / 2 ^ 64 = 0) := by
  have hiff := umulh_ten_eq_zero_iff acc
  change (BitVec.truncate 64 ((BitVec.zeroExtend 128 acc * 10#128) >>> 64) = 0#64) ↔ _ at hiff
  rw [Bool.eq_iff_iff, beq_iff_eq, eq_comm, decide_eq_true_eq]
  exact hiff

private theorem cells2_to_memRegion16 (p v0 v1 : BitVec 64) :
    ((p ↦₆₄ v0) ∗ ((p + 8#64) ↦₆₄ v1)) ⊢ memRegion p 16 := by
  rw [memRegion_split' (b := p) (b' := p + 8#64) (n := 8) (k := 8) rfl rfl (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)

private theorem cells3_to_memRegion24 (p v0 v1 v2 : BitVec 64) :
    ((p ↦₆₄ v0) ∗ ((p + 8#64) ↦₆₄ v1) ∗ ((p + 16#64) ↦₆₄ v2)) ⊢ memRegion p 24 := by
  rw [memRegion_split' (b := p) (b' := p + 8#64) (n := 8) (k := 16) rfl rfl (by decide),
      memRegion_split' (b := p + 8#64) (b' := p + 16#64) (n := 8) (k := 8) rfl (by bv_lin) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))

private theorem outSlot_none_pack (outPtr o1 o2 o3 : BitVec 64) (R F : SepProp) :
    (R ∗ (outPtr ↦₆₄ 0#64) ∗ ((outPtr + 8#64) ↦₆₄ o1) ∗
      ((outPtr + 16#64) ↦₆₄ o2) ∗ ((outPtr + 24#64) ↦₆₄ o3) ∗ F) ⊢
    (R ∗ (outPtr ↦₆₄ 0#64) ∗ memRegion (outPtr + 8#64) 24 ∗ F) := by
  have h3 : (((outPtr + 8#64) ↦₆₄ o1) ∗ ((outPtr + 16#64) ↦₆₄ o2) ∗ ((outPtr + 24#64) ↦₆₄ o3)) ⊢
      memRegion (outPtr + 8#64) 24 := by
    rw [memRegion_split' (b := outPtr + 8#64) (b' := outPtr + 16#64) (n := 8) (k := 16) rfl (by bv_lin) (by decide),
        memRegion_split' (b := outPtr + 16#64) (b' := outPtr + 24#64) (n := 8) (k := 8) rfl (by bv_lin) (by decide)]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))
  refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h3)))
  sep_entail

theorem hbSplitOnceSpace_wp {Q : Program} {C : HbCliLayout}
    {target ret_pc restPtr outPtr : BitVec 64} {rest : List (BitVec 8)}
    {s0 : State} {F : SepProp} {post : State → SepProp → Prop}
    (hc : CodeChunks Q (hbSplitOnceSpaceChunks C))
    (_hptr_nz : restPtr ≠ 0#64) (hptr_fit : restPtr.toNat + rest.length < 2 ^ 64)
    (hpc : s0.pc = C.splitOnceSpaceAddr) (hrun : s0.status = .Running)
    (hlr : s0.readReg64 Reg.lr = ret_pc)
    (hx0 : s0.readReg64 .x0 = restPtr) (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 rest.length)
    (hx8 : s0.readReg64 .x8 = outPtr)
    (hSome : ∀ (sf : State) (k : Nat) (_hk : k < rest.length),
      splitFirstByte 0x20#8 rest = some (rest.take k, rest.drop (k + 1)) →
      sf.pc = ret_pc → sf.status = .Running → PureCpuStep s0 sf →
      SepWP Q target sf
        ((restPtr ↦ₛ rest) ∗ (outPtr ↦₆₄ restPtr) ∗ ((outPtr + 8#64) ↦₆₄ BitVec.ofNat 64 k) ∗
         ((outPtr + 16#64) ↦₆₄ (restPtr + BitVec.ofNat 64 (k + 1))) ∗
         ((outPtr + 24#64) ↦₆₄ BitVec.ofNat 64 (rest.drop (k + 1)).length) ∗ F) post)
    (hNone : ∀ sf : State,
      splitFirstByte 0x20#8 rest = none →
      sf.pc = ret_pc → sf.status = .Running → PureCpuStep s0 sf →
      SepWP Q target sf ((restPtr ↦ₛ rest) ∗ (outPtr ↦₆₄ 0#64) ∗ memRegion (outPtr + 8#64) 24 ∗ F) post) :
    SepWP Q target s0 ((restPtr ↦ₛ rest) ∗ memRegion outPtr 32 ∗ F) post := by
  have hc0 : Q.hasCode C.splitOnceSpaceAddr hbSplitOnceSpaceWords := hc
  have hlen : rest.length < 2 ^ 64 := by omega
  conv => arg 4; rw [show (32 : Nat) = 8 * 4 from rfl, memRegion_cells outPtr 4 (by decide),
    cells_succ, cells_succ, cells_succ, cells_succ, cells_zero]
  conv => arg 4; simp only [sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, show (8#64 : BitVec 64) + 8#64 = 16#64 by decide,
    show (16#64 : BitVec 64) + 8#64 = 24#64 by decide]
  iterate 4 (apply SepWP.exists_left; intro _)
  rcases rest with _ | ⟨b0, r0⟩
  · wp_steps 3
    exact SepWP.weaken_pre (Entails.trans (by sep_entail) (outSlot_none_pack outPtr _ _ _ _ _))
      (hNone _ (splitFirstByte_nil 0x20#8) wp_a (by simp [wp_norm, arm64_norm, hrun]) (close_cpu_step s0))
  · have hnz : (BitVec.ofNat 64 (b0 :: r0).length == 0#64) = false := by
      rw [beq_eq_false_iff_ne]; intro he; have ht := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen] at ht; simp at ht
    wp_steps 2
    exact SepWP.weaken_pre (by sep_frame)
      (splitOnceSpace_loop_wp hc0 (fuel := (b0 :: r0).length) (idx := 0)
        (by omega) (by simp) hlen (fun _ hj => by omega)
        wp_a (by simp [wp_norm, arm64_norm, hrun]) wp_a wp_a wp_a wp_a wp_a
        (fun sf k hk h1 h2 h3 h4 => hSome sf k hk h1 h2 h3 (PureCpuStep.trans (close_cpu_step s0) h4))
        (fun sf h1 h2 h3 h4 => SepWP.weaken_pre (outSlot_none_pack outPtr _ _ _ _ _)
          (hNone sf h1 h2 h3 (PureCpuStep.trans (close_cpu_step s0) h4))))

private theorem parseDecimal_loop_wp {Q : Program} {C : HbCliLayout}
    {target ret_pc ptr acc : BitVec 64} {bs : List (BitVec 8)} {s0 : State} {F : SepProp}
    {post : State → SepProp → Prop}
    (hc : Q.hasCode C.parseDecimalU64Addr hbParseDecimalU64Words) (hlen : bs.length < 2 ^ 64)
    (hpc : s0.pc = C.parseDecimalU64Addr + 0x10#64) (hrun : s0.status = .Running)
    (hlr : s0.readReg64 Reg.lr = ret_pc)
    (hx0 : s0.readReg64 .x0 = ptr) (hx8 : s0.readReg64 .x8 = BitVec.ofNat 64 bs.length)
    (hx1 : s0.readReg64 .x1 = acc) (hx10 : s0.readReg64 .x10 = 10#64)
    (hOk : ∀ (sf : State) (n : Nat), parseDecimalFold acc.toNat bs = some n →
      sf.pc = ret_pc → sf.status = .Running → PureCpuStep s0 sf →
      sf.readReg64 .x0 = 1#64 → sf.readReg64 .x1 = BitVec.ofNat 64 n →
      SepWP Q target sf ((ptr ↦ₛ bs) ∗ F) post)
    (hErr : ∀ sf : State, parseDecimalFold acc.toNat bs = none →
      sf.pc = ret_pc → sf.status = .Running → PureCpuStep s0 sf →
      sf.readReg64 .x0 = 0#64 → SepWP Q target sf ((ptr ↦ₛ bs) ∗ F) post) :
    SepWP Q target s0 ((ptr ↦ₛ bs) ∗ F) post := by
  induction bs generalizing ptr acc s0 F with
  | nil =>
    wp_steps 4; exact hOk _ acc.toNat rfl wp_a (by simp [wp_norm, arm64_norm, hrun])
      (close_cpu_step s0) wp_a (by simp [wp_norm, arm64_norm, hx1, BitVec.ofNat_toNat])
  | cons b rest ih =>
    have hnz : (BitVec.ofNat 64 (b :: rest).length == 0#64) = false := by
      rw [beq_eq_false_iff_ne]; intro he; have ht := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen] at ht; simp at ht
    conv => arg 4; rw [pointsToBytes_cons]
    wp_steps 4
    by_cases hdig : (0x30#8 ≤ b && b ≤ 0x39#8) = true
    · have hhi : (9#32).ult (b.zeroExtend 32 - 0x30#32) = false := by rw [digit_ult_nine, hdig]; rfl
      have hm10 : ((acc + (acc <<< 2)) <<< 1) = acc * 10#64 := mulTen_shift_eq acc
      by_cases hum : (acc.toNat * 10) / 2 ^ 64 = 0
      · have hum0 : (0#64 == BitVec.truncate 64 ((BitVec.zeroExtend 128 acc * 10#128) >>> 64)) = true := by
          rw [umulh_beq_zero]; exact decide_eq_true hum
        have hsub_len : BitVec.ofNat 64 (b :: rest).length - 1#64 = BitVec.ofNat 64 rest.length := by
          rw [List.length_cons, BitVec.ofNat_add]; bv_lin
        by_cases hadd :
            (acc * 10#64).toNat + (((b.zeroExtend 32 - 0x30#32).zeroExtend 8).zeroExtend 64).toNat < 2 ^ 64
        · have hule : (acc * 10#64).ule
              (acc * 10#64 + ((b.zeroExtend 32 - 0x30#32).zeroExtend 8).zeroExtend 64) = true := by
            rw [add_ule_left]; exact decide_eq_true hadd
          wp_steps 12
          have hfold := parseDecimalFold_cons_valid_ok rest hdig (digitSub_uxtb_toNat_of_le_nine hdig) ⟨hum, hadd⟩
          exact SepWP.weaken_pre (by sep_frame) (ih (ptr := ptr + 1#64)
            (acc := acc * 10#64 + ((b.zeroExtend 32 - 0x30#32).zeroExtend 8).zeroExtend 64)
            (F := (ptr ↦₈ b) ∗ F) (by simp at hlen; omega) wp_a (by simp [wp_norm, arm64_norm, hrun])
            wp_a wp_a wp_a wp_a wp_a
            (fun sf n hfn h1 h2 h3 h4 h5 => SepWP.weaken_pre (by rw [pointsToBytes_cons]; sep_frame)
              (hOk sf n (hfold.trans hfn) h1 h2 (PureCpuStep.trans (close_cpu_step s0) h3) h4 h5))
            (fun sf hfn h1 h2 h3 h4 => SepWP.weaken_pre (by rw [pointsToBytes_cons]; sep_frame)
              (hErr sf (hfold.trans hfn) h1 h2 (PureCpuStep.trans (close_cpu_step s0) h3) h4)))
        · have hule : (acc * 10#64).ule
              (acc * 10#64 + ((b.zeroExtend 32 - 0x30#32).zeroExtend 8).zeroExtend 64) = false := by
            rw [add_ule_left]; exact decide_eq_false hadd
          wp_steps 15; conv => arg 4; rw [← pointsToBytes_cons]
          exact hErr _ (parseDecimalFold_cons_valid_overflow rest hdig
            (digitSub_uxtb_toNat_of_le_nine hdig) (fun h => hadd h.2))
            wp_a (by simp [wp_norm, arm64_norm, hrun]) (close_cpu_step s0) wp_a
      · have hum0 : (0#64 == BitVec.truncate 64 ((BitVec.zeroExtend 128 acc * 10#128) >>> 64)) = false := by
          rw [umulh_beq_zero]; exact decide_eq_false hum
        wp_steps 12; conv => arg 4; rw [← pointsToBytes_cons]
        exact hErr _ (parseDecimalFold_cons_valid_overflow rest hdig
          (digitSub_uxtb_toNat_of_le_nine hdig) (fun h => hum h.1))
          wp_a (by simp [wp_norm, arm64_norm, hrun]) (close_cpu_step s0) wp_a
    · have hhi : (9#32).ult (b.zeroExtend 32 - 0x30#32) = true := by
        rw [digit_ult_nine, Bool.eq_false_iff.mpr hdig]; rfl
      wp_steps 4; conv => arg 4; rw [← pointsToBytes_cons]
      exact hErr _ (parseDecimalFold_cons_invalid acc.toNat rest hdig)
        wp_a (by simp [wp_norm, arm64_norm, hrun]) (close_cpu_step s0) wp_a

theorem hbParseDecimalU64_wp {Q : Program} {C : HbCliLayout} {target ret_pc ptr : BitVec 64}
    {bs : List (BitVec 8)} {s0 : State} {F : SepProp} {post : State → SepProp → Prop}
    (hc : CodeChunks Q (hbParseDecimalU64Chunks C)) (hlen : bs.length < 2 ^ 64)
    (hpc : s0.pc = C.parseDecimalU64Addr) (hrun : s0.status = .Running)
    (hlr : s0.readReg64 Reg.lr = ret_pc)
    (hx0 : s0.readReg64 .x0 = ptr) (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 bs.length)
    (hSome : ∀ (sf : State) (v : BitVec 64), parseDecimalU64 bs = some v →
      sf.pc = ret_pc → sf.status = .Running → PureCpuStep s0 sf →
      sf.readReg64 .x0 = 1#64 → sf.readReg64 .x1 = v →
      SepWP Q target sf ((ptr ↦ₛ bs) ∗ F) post)
    (hNone : ∀ sf : State, parseDecimalU64 bs = none →
      sf.pc = ret_pc → sf.status = .Running → PureCpuStep s0 sf →
      sf.readReg64 .x0 = 0#64 → SepWP Q target sf ((ptr ↦ₛ bs) ∗ F) post) :
    SepWP Q target s0 ((ptr ↦ₛ bs) ∗ F) post := by
  have hc0 : Q.hasCode C.parseDecimalU64Addr hbParseDecimalU64Words := hc
  rcases bs with _ | ⟨b0, r0⟩
  · wp_steps 4
    exact hNone _ parseDecimalU64_nil wp_a (by simp [wp_norm, arm64_norm, hrun])
      (close_cpu_step s0) wp_a
  · have hnz : (BitVec.ofNat 64 (b0 :: r0).length == 0#64) = false := by
      rw [beq_eq_false_iff_ne]; intro he; have ht := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen] at ht; simp at ht
    wp_steps 4
    exact parseDecimal_loop_wp hc0 (acc := 0#64) hlen wp_a (by simp [wp_norm, arm64_norm, hrun])
      wp_a wp_a wp_a wp_a wp_a
      (fun sf n hfn h1 h2 h3 h4 h5 => hSome sf (BitVec.ofNat 64 n)
        (by rw [parseDecimalU64_of_nonempty (by simp)]; exact congrArg (Option.map (BitVec.ofNat 64)) hfn)
        h1 h2 (PureCpuStep.trans (close_cpu_step s0) h3) h4 h5)
      (fun sf hfn h1 h2 h3 h4 => hNone sf
        (by rw [parseDecimalU64_of_nonempty (by simp)]; exact congrArg (Option.map (BitVec.ofNat 64)) hfn)
        h1 h2 (PureCpuStep.trans (close_cpu_step s0) h3) h4)

/-- Read-only `.rodata` command prefixes and literals read by `parse_command`. -/
def HbParseRoData (C : HbCliLayout) : SepProp :=
  (C.pfxInsertAddr ↦ᵣ pfxInsertBytes) ∗ (C.pfxRemoveAddr ↦ᵣ pfxRemoveBytes) ∗
  (C.pfxGetAddr ↦ᵣ pfxGetBytes) ∗ (C.pfxContainsAddr ↦ᵣ pfxContainsBytes) ∗
  (C.pfxWithCapAddr ↦ᵣ pfxWithCapBytes) ∗ (C.cmdLenAddr ↦ᵣ cmdLenBytes) ∗
  (C.cmdIsEmptyAddr ↦ᵣ cmdIsEmptyBytes) ∗ (C.cmdClearAddr ↦ᵣ cmdClearBytes)

/-- Postcondition relation between `parseCommand line` and the 3-word output slot `(r0, r1, r2)`. -/
def ParseCmdSlot : Option CliCmd → BitVec 64 → BitVec 64 → BitVec 64 → Prop
  | none                  , r0, _ , _  => r0 = 0xffffffffffffffff#64
  | some (.insert k v)    , r0, r1, r2 => r0 = 0#64 ∧ r1 = k ∧ r2 = v
  | some (.get k)         , r0, r1, _  => r0 = 1#64 ∧ r1 = k
  | some (.remove k)      , r0, r1, _  => r0 = 2#64 ∧ r1 = k
  | some (.contains k)    , r0, r1, _  => r0 = 3#64 ∧ r1 = k
  | some (.withCapacity n), r0, r1, _  => r0 = 4#64 ∧ r1 = n ∧ n.toNat ≤ MaxWithCapacity
  | some .len             , r0, _ , _  => r0 = 5#64
  | some .isEmpty         , r0, _ , _  => r0 = 6#64
  | some .clear           , r0, _ , _  => r0 = 7#64

private def ParseCmdFrame (s0 s : State) : Prop :=
  s.sp = s0.sp - 80#64 ∧ s.spAligned = true ∧
  s.fs = s0.fs ∧ s.trace = s0.trace ∧ CpuAuxPreserved s0 s ∧
  calleeSavedVRegs s = calleeSavedVRegs s0 ∧
  s.readReg64 .x23 = s0.readReg64 .x23 ∧ s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧ s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧ s.readReg64 .x28 = s0.readReg64 .x28

private theorem ParseCmdFrame.of_cpu {s0 s1 s2 : State}
    (hf : ParseCmdFrame s0 s1) (hcpu : PureCpuStep s1 s2) : ParseCmdFrame s0 s2 := by
  rcases hf with ⟨hsp, hal, hfs, htr, haux, hv, r23, r24, r25, r26, r27, r28⟩
  rcases hcpu with ⟨hsp2, hfs2, htr2, haux2, hcs2⟩
  exact ⟨hsp2.trans hsp, by simpa [State.spAligned, hsp2] using hal,
    hfs2.trans hfs, htr2.trans htr, haux.trans haux2, hcs2.vregs.trans hv,
    hcs2.readReg64_x23.trans r23, hcs2.readReg64_x24.trans r24,
    hcs2.readReg64_x25.trans r25, hcs2.readReg64_x26.trans r26,
    hcs2.readReg64_x27.trans r27, hcs2.readReg64_x28.trans r28⟩

private theorem ParseCmdFrame.step {s0 s1 s2 : State}
    (hf : ParseCmdFrame s0 s1)
    (hsp : s2.sp = s1.sp) (hfs : s2.fs = s1.fs) (htr : s2.trace = s1.trace)
    (haux : CpuAuxPreserved s1 s2) (hv : calleeSavedVRegs s2 = calleeSavedVRegs s1)
    (r23 : s2.readReg64 .x23 = s1.readReg64 .x23) (r24 : s2.readReg64 .x24 = s1.readReg64 .x24)
    (r25 : s2.readReg64 .x25 = s1.readReg64 .x25) (r26 : s2.readReg64 .x26 = s1.readReg64 .x26)
    (r27 : s2.readReg64 .x27 = s1.readReg64 .x27) (r28 : s2.readReg64 .x28 = s1.readReg64 .x28) :
    ParseCmdFrame s0 s2 := by
  rcases hf with ⟨hsp0, hal0, hfs0, htr0, haux0, hv0, x23, x24, x25, x26, x27, x28⟩
  exact ⟨hsp.trans hsp0, by simpa [State.spAligned, hsp] using hal0,
    hfs.trans hfs0, htr.trans htr0, haux0.trans haux, hv.trans hv0,
    r23.trans x23, r24.trans x24, r25.trans x25, r26.trans x26, r27.trans x27, r28.trans x28⟩

local macro "close_parse_frame " hf:term : term =>
  `(ParseCmdFrame.step $hf (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm]) (by simp [CpuAuxPreserved.refl _])
      (by simp [calleeSavedVRegs, wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]))

private def parseCmdSavedRegs (sp0 : BitVec 64) (s0 : State) : SepProp :=
  ((sp0 - 48#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp0 - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
  ((sp0 - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp0 - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp0 - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp0 - 8#64) ↦₆₄ s0.readReg64 .x19)

private theorem parseCmd_stack_unpack (sp0 : BitVec 64) :
    stackAt sp0 128 =
      cells (sp0 - 48#64) 6 ∗ memRegion (sp0 - 80#64) 32 ∗ stackAt (sp0 - 80#64) 48 := by
  have h1 := stackAt_split (sp := sp0) 80 48
  have h2 := stackAt_split (sp := sp0) 48 32
  have h3 : stackAt (sp0 - 48#64) 32 = memRegion (sp0 - 80#64) 32 := by
    unfold stackAt; congr 1; bv_lin
  have h4 := stackAt_eq_cells sp0 6
  change stackAt sp0 48 = cells (sp0 - 48#64) 6 at h4
  change stackAt sp0 128 = _ at h1; change stackAt sp0 80 = _ at h2
  rw [h1, h2, h3, h4, sepConj_assoc]

private theorem parseCmd_stack_repack (sp0 : BitVec 64) (s0 : State) :
    parseCmdSavedRegs sp0 s0 ∗ memRegion (sp0 - 80#64) 32 ∗ stackAt (sp0 - 80#64) 48 ⊢
      stackAt sp0 128 := by
  rw [parseCmd_stack_unpack sp0]
  refine sepConj_mono_left ?_
  unfold parseCmdSavedRegs
  cells_unfold
  apply Entails.sepExists_right (s0.readReg64 .x29)
  apply Entails.sepExists_right (s0.readReg64 Reg.lr)
  apply Entails.sepExists_right (s0.readReg64 .x22)
  apply Entails.sepExists_right (s0.readReg64 .x21)
  apply Entails.sepExists_right (s0.readReg64 .x20)
  apply Entails.sepExists_right (s0.readReg64 .x19)
  sep_entail

private theorem cell_memRegion24_to_32 (p v : BitVec 64) :
    (p ↦₆₄ v) ∗ memRegion (p + 8#64) 24 ⊢ memRegion p 32 := by
  rw [memRegion_split' (b := p) (b' := p + 8#64) (n := 8) (k := 24) rfl rfl (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion p v)

private theorem cells4_to_memRegion32 (p v0 v1 v2 v3 : BitVec 64) :
    ((p ↦₆₄ v0) ∗ ((p + 8#64) ↦₆₄ v1) ∗ ((p + 16#64) ↦₆₄ v2) ∗ ((p + 24#64) ↦₆₄ v3)) ⊢
      memRegion p 32 := by
  refine Entails.trans (sepConj_mono_right ?_) (cell_memRegion24_to_32 p v0)
  have h3 := cells3_to_memRegion24 (p + 8#64) v1 v2 v3
  simpa only [BitVec.add_assoc, show (8#64 : BitVec 64) + 8#64 = 16#64 by decide,
    show (8#64 : BitVec 64) + 16#64 = 24#64 by decide] using h3

private theorem parseCmd_epilogue_wp {Q : Program} {C : HbCliLayout}
    {target ret_pc linePtr outPtr r0 r1 r2 : BitVec 64} {line : List (BitVec 8)}
    {s0 s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hcP : CodeChunks Q (hbParseCommandChunks C))
    (hlr0 : s0.readReg64 Reg.lr = ret_pc)
    (hpc : s.pc = C.parseCommandAddr + 0x1a4#64) (hrun : s.status = .Running)
    (hf : ParseCmdFrame s0 s) (hslot : ParseCmdSlot (parseCommand line) r0 r1 r2)
    (hNext : ∀ (sf : State) (r0' r1' r2' : BitVec 64),
      ParseCmdSlot (parseCommand line) r0' r1' r2' →
      sf.pc = ret_pc → sf.status = .Running → PureCpuStep s0 sf →
      SepWP Q target sf
        ((linePtr ↦ₛ line) ∗ (outPtr ↦₆₄ r0') ∗ ((outPtr + 8#64) ↦₆₄ r1') ∗
         ((outPtr + 16#64) ↦₆₄ r2') ∗ HbParseRoData C ∗ stackAt s0.sp 128 ∗ F) post) :
    SepWP Q target s
      ((linePtr ↦ₛ line) ∗ (outPtr ↦₆₄ r0) ∗ ((outPtr + 8#64) ↦₆₄ r1) ∗
       ((outPtr + 16#64) ↦₆₄ r2) ∗ HbParseRoData C ∗
       parseCmdSavedRegs s0.sp s0 ∗ memRegion (s0.sp - 80#64) 32 ∗
       stackAt (s0.sp - 80#64) 48 ∗ F) post := by
  unpack_cmd_code hbParseCommandChunks hcP
  rcases hf with ⟨hsp, hsp_al, hfs, htr, haux, hv, r23, r24, r25, r26, r27, r28⟩
  dsimp only [parseCmdSavedRegs]
  wp_steps 5
  have hrepack :
      ((linePtr ↦ₛ line) ∗ (outPtr ↦₆₄ r0) ∗ ((outPtr + 8#64) ↦₆₄ r1) ∗
       ((outPtr + 16#64) ↦₆₄ r2) ∗ HbParseRoData C ∗
       parseCmdSavedRegs s0.sp s0 ∗ memRegion (s0.sp - 80#64) 32 ∗
       stackAt (s0.sp - 80#64) 48 ∗ F) ⊢
      ((linePtr ↦ₛ line) ∗ (outPtr ↦₆₄ r0) ∗ ((outPtr + 8#64) ↦₆₄ r1) ∗
       ((outPtr + 16#64) ↦₆₄ r2) ∗ HbParseRoData C ∗ stackAt s0.sp 128 ∗ F) := by
    have hsr := parseCmd_stack_repack s0.sp s0
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left hsr))))))
    sep_entail
  refine SepWP.weaken_pre (Entails.trans (by unfold parseCmdSavedRegs; sep_entail) hrepack)
    (hNext _ r0 r1 r2 hslot wp_a (by simp [wp_norm, arm64_norm, hrun])
      ⟨wp_a,
       by simp [wp_norm, arm64_norm, hfs],
       by simp [wp_norm, arm64_norm, htr],
       haux.trans (by simp [CpuAuxPreserved.refl s]),
       by close_cs⟩)

private theorem parseCmd_storeTag_wp {Q : Program} {C : HbCliLayout}
    {target ret_pc linePtr outPtr tag c0 c1 c2 : BitVec 64} {line : List (BitVec 8)}
    {s0 s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hcP : CodeChunks Q (hbParseCommandChunks C)) (hlr0 : s0.readReg64 Reg.lr = ret_pc)
    (hpc : s.pc = C.parseCommandAddr + 0x1a0#64) (hrun : s.status = .Running)
    (hf : ParseCmdFrame s0 s) (hx19 : s.readReg64 .x19 = outPtr) (hx8 : s.readReg64 .x8 = tag)
    (hslot : ParseCmdSlot (parseCommand line) tag c1 c2)
    (hNext : ∀ (sf : State) (r0' r1' r2' : BitVec 64),
      ParseCmdSlot (parseCommand line) r0' r1' r2' →
      sf.pc = ret_pc → sf.status = .Running → PureCpuStep s0 sf →
      SepWP Q target sf
        ((linePtr ↦ₛ line) ∗ (outPtr ↦₆₄ r0') ∗ ((outPtr + 8#64) ↦₆₄ r1') ∗
         ((outPtr + 16#64) ↦₆₄ r2') ∗ HbParseRoData C ∗ stackAt s0.sp 128 ∗ F) post) :
    SepWP Q target s
      ((linePtr ↦ₛ line) ∗ (outPtr ↦₆₄ c0) ∗ ((outPtr + 8#64) ↦₆₄ c1) ∗
       ((outPtr + 16#64) ↦₆₄ c2) ∗ HbParseRoData C ∗
       parseCmdSavedRegs s0.sp s0 ∗ memRegion (s0.sp - 80#64) 32 ∗
       stackAt (s0.sp - 80#64) 48 ∗ F) post := by
  unpack_cmd_code hbParseCommandChunks hcP
  wp_steps 1
  exact parseCmd_epilogue_wp hcP hlr0 wp_a (by simp [wp_norm, arm64_norm, hrun])
    (hf.of_cpu (close_cpu_step s)) hslot hNext

private theorem parseCmd_none_wp {Q : Program} {C : HbCliLayout}
    {target ret_pc linePtr outPtr c0 c1 c2 : BitVec 64} {line : List (BitVec 8)}
    {s0 s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hcP : CodeChunks Q (hbParseCommandChunks C)) (hlr0 : s0.readReg64 Reg.lr = ret_pc)
    (hpc : s.pc = C.parseCommandAddr + 0x19c#64) (hrun : s.status = .Running)
    (hf : ParseCmdFrame s0 s) (hx19 : s.readReg64 .x19 = outPtr)
    (hnone : parseCommand line = none)
    (hNext : ∀ (sf : State) (r0' r1' r2' : BitVec 64),
      ParseCmdSlot (parseCommand line) r0' r1' r2' →
      sf.pc = ret_pc → sf.status = .Running → PureCpuStep s0 sf →
      SepWP Q target sf
        ((linePtr ↦ₛ line) ∗ (outPtr ↦₆₄ r0') ∗ ((outPtr + 8#64) ↦₆₄ r1') ∗
         ((outPtr + 16#64) ↦₆₄ r2') ∗ HbParseRoData C ∗ stackAt s0.sp 128 ∗ F) post) :
    SepWP Q target s
      ((linePtr ↦ₛ line) ∗ (outPtr ↦₆₄ c0) ∗ ((outPtr + 8#64) ↦₆₄ c1) ∗
       ((outPtr + 16#64) ↦₆₄ c2) ∗ HbParseRoData C ∗
       parseCmdSavedRegs s0.sp s0 ∗ memRegion (s0.sp - 80#64) 32 ∗
       stackAt (s0.sp - 80#64) 48 ∗ F) post := by
  unpack_cmd_code hbParseCommandChunks hcP
  wp_steps 1
  exact parseCmd_storeTag_wp hcP hlr0 wp_a (by simp [wp_norm, arm64_norm, hrun])
    (hf.of_cpu (close_cpu_step s)) wp_a (rfl) (by simp [ParseCmdSlot, hnone]) hNext

private theorem parseCmd_storePair_wp {Q : Program} {C : HbCliLayout}
    {target ret_pc linePtr outPtr tag val c0 c1 c2 : BitVec 64} {line : List (BitVec 8)}
    {s0 s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hcP : CodeChunks Q (hbParseCommandChunks C)) (hlr0 : s0.readReg64 Reg.lr = ret_pc)
    (hpc : s.pc = C.parseCommandAddr + 0xf4#64) (hrun : s.status = .Running)
    (hf : ParseCmdFrame s0 s) (hx19 : s.readReg64 .x19 = outPtr)
    (hx8 : s.readReg64 .x8 = tag) (hx1 : s.readReg64 .x1 = val)
    (hslot : ParseCmdSlot (parseCommand line) tag val c2)
    (hNext : ∀ (sf : State) (r0' r1' r2' : BitVec 64),
      ParseCmdSlot (parseCommand line) r0' r1' r2' →
      sf.pc = ret_pc → sf.status = .Running → PureCpuStep s0 sf →
      SepWP Q target sf
        ((linePtr ↦ₛ line) ∗ (outPtr ↦₆₄ r0') ∗ ((outPtr + 8#64) ↦₆₄ r1') ∗
         ((outPtr + 16#64) ↦₆₄ r2') ∗ HbParseRoData C ∗ stackAt s0.sp 128 ∗ F) post) :
    SepWP Q target s
      ((linePtr ↦ₛ line) ∗ (outPtr ↦₆₄ c0) ∗ ((outPtr + 8#64) ↦₆₄ c1) ∗
       ((outPtr + 16#64) ↦₆₄ c2) ∗ HbParseRoData C ∗
       parseCmdSavedRegs s0.sp s0 ∗ memRegion (s0.sp - 80#64) 32 ∗
       stackAt (s0.sp - 80#64) 48 ∗ F) post := by
  unpack_cmd_code hbParseCommandChunks hcP
  wp_steps 2
  exact parseCmd_epilogue_wp hcP hlr0 wp_a (by simp [wp_norm, arm64_norm, hrun])
    (hf.of_cpu (close_cpu_step s)) hslot hNext

private theorem parseCmd_exact_wp {Q : Program} {C : HbCliLayout}
    {target ret_pc linePtr outPtr c0 c1 c2 : BitVec 64} {line : List (BitVec 8)}
    {s0 s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hcP : CodeChunks Q (hbParseCommandChunks C)) (hcB : CodeChunks Q (hbBytesEqChunks C))
    (hlr0 : s0.readReg64 Reg.lr = ret_pc) (hlen : line.length < 2 ^ 64)
    (h1 : stripBytePrefix pfxInsertBytes line = none)
    (h2 : stripBytePrefix pfxRemoveBytes line = none)
    (h3 : stripBytePrefix pfxGetBytes line = none)
    (h4 : stripBytePrefix pfxContainsBytes line = none)
    (h5 : stripBytePrefix pfxWithCapBytes line = none)
    (hpc : s.pc = C.parseCommandAddr + 0x130#64) (hrun : s.status = .Running)
    (hf : ParseCmdFrame s0 s) (hx19 : s.readReg64 .x19 = outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 line.length) (hx21 : s.readReg64 .x21 = linePtr)
    (hNext : ∀ (sf : State) (r0' r1' r2' : BitVec 64),
      ParseCmdSlot (parseCommand line) r0' r1' r2' →
      sf.pc = ret_pc → sf.status = .Running → PureCpuStep s0 sf →
      SepWP Q target sf
        ((linePtr ↦ₛ line) ∗ (outPtr ↦₆₄ r0') ∗ ((outPtr + 8#64) ↦₆₄ r1') ∗
         ((outPtr + 16#64) ↦₆₄ r2') ∗ HbParseRoData C ∗ stackAt s0.sp 128 ∗ F) post) :
    SepWP Q target s
      ((linePtr ↦ₛ line) ∗ (outPtr ↦₆₄ c0) ∗ ((outPtr + 8#64) ↦₆₄ c1) ∗
       ((outPtr + 16#64) ↦₆₄ c2) ∗ HbParseRoData C ∗
       parseCmdSavedRegs s0.sp s0 ∗ memRegion (s0.sp - 80#64) 32 ∗
       stackAt (s0.sp - 80#64) 48 ∗ F) post := by
  have hp_eq := parseCommand_of_no_pfx h1 h2 h3 h4 h5
  unpack_cmd_code hbParseCommandChunks hcP
  wp_steps 1; wp_steps 1; wp_steps 3; wp_steps 1; norm_jmp
  dsimp only [HbParseRoData]
  refine SepWP.weaken_pre (by sep_frame)
    (hbBytesEq_wp hcB (bs1 := line) (bs2 := cmdLenBytes)
      (ret_pc := C.parseCommandAddr + 0x148#64) hlen (by decide)
      wp_a (by simp [wp_norm, arm64_norm, hrun]) wp_a wp_a wp_a wp_a rfl
      fun s1 hpc1 hrun1 hcpu1 hx0_1 => ?_)
  have hf1 : ParseCmdFrame s0 s1 := hf.of_cpu (PureCpuStep.trans (close_cpu_step s) hcpu1)
  have hx19_1 : s1.readReg64 .x19 = outPtr := hcpu1.2.2.2.2.readReg64_x19.trans wp_a
  have hx20_1 : s1.readReg64 .x20 = BitVec.ofNat 64 line.length :=
    hcpu1.2.2.2.2.readReg64_x20.trans wp_a
  have hx21_1 : s1.readReg64 .x21 = linePtr := hcpu1.2.2.2.2.readReg64_x21.trans wp_a
  by_cases hlen_eq : (line == cmdLenBytes) = true
  · simp only [hlen_eq, ↓reduceIte] at hx0_1 hp_eq
    have hx0_1' : s1.readReg64 (.gpr 0#5) = 1#64 := hx0_1
    wp_steps 3
    refine SepWP.weaken_pre (by unfold HbParseRoData; sep_entail)
      (parseCmd_storeTag_wp hcP hlr0 wp_a (by simp [wp_norm, arm64_norm, hrun1])
        (hf1.of_cpu (close_cpu_step s1)) wp_a rfl (by simp [ParseCmdSlot, hp_eq]) hNext)
  · simp only [hlen_eq, Bool.false_eq_true, ↓reduceIte] at hx0_1 hp_eq
    have hx0_1' : s1.readReg64 (.gpr 0#5) = 0#64 := hx0_1
    wp_steps 2; wp_steps 1; wp_steps 3; wp_steps 1; norm_jmp
    refine SepWP.weaken_pre (by sep_frame)
      (hbBytesEq_wp hcB (bs1 := line) (bs2 := cmdIsEmptyBytes)
        (ret_pc := C.parseCommandAddr + 0x16c#64) hlen (by decide)
        wp_a (by simp [wp_norm, arm64_norm, hrun1]) wp_a wp_a wp_a wp_a rfl
        fun s2 hpc2 hrun2 hcpu2 hx0_2 => ?_)
    have hf2 : ParseCmdFrame s0 s2 := hf1.of_cpu (PureCpuStep.trans (close_cpu_step s1) hcpu2)
    have hx19_2 : s2.readReg64 .x19 = outPtr := hcpu2.2.2.2.2.readReg64_x19.trans wp_a
    have hx20_2 : s2.readReg64 .x20 = BitVec.ofNat 64 line.length :=
      hcpu2.2.2.2.2.readReg64_x20.trans wp_a
    have hx21_2 : s2.readReg64 .x21 = linePtr := hcpu2.2.2.2.2.readReg64_x21.trans wp_a
    by_cases hemp_eq : (line == cmdIsEmptyBytes) = true
    · simp only [hemp_eq, ↓reduceIte] at hx0_2 hp_eq
      have hx0_2' : s2.readReg64 (.gpr 0#5) = 1#64 := hx0_2
      wp_steps 3
      refine SepWP.weaken_pre (by unfold HbParseRoData; sep_entail)
        (parseCmd_storeTag_wp hcP hlr0 wp_a (by simp [wp_norm, arm64_norm, hrun2])
          (hf2.of_cpu (close_cpu_step s2)) wp_a rfl (by simp [ParseCmdSlot, hp_eq]) hNext)
    · simp only [hemp_eq, Bool.false_eq_true, ↓reduceIte] at hx0_2 hp_eq
      have hx0_2' : s2.readReg64 (.gpr 0#5) = 0#64 := hx0_2
      wp_steps 2; wp_steps 1; wp_steps 3; wp_steps 1; norm_jmp
      refine SepWP.weaken_pre (by sep_frame)
        (hbBytesEq_wp hcB (bs1 := line) (bs2 := cmdClearBytes)
          (ret_pc := C.parseCommandAddr + 0x190#64) hlen (by decide)
          wp_a (by simp [wp_norm, arm64_norm, hrun2]) wp_a wp_a wp_a wp_a rfl
          fun s3 hpc3 hrun3 hcpu3 hx0_3 => ?_)
      have hf3 : ParseCmdFrame s0 s3 := hf2.of_cpu (PureCpuStep.trans (close_cpu_step s2) hcpu3)
      have hx19_3 : s3.readReg64 .x19 = outPtr := hcpu3.2.2.2.2.readReg64_x19.trans wp_a
      by_cases hclr_eq : (line == cmdClearBytes) = true
      · simp only [hclr_eq, ↓reduceIte] at hx0_3 hp_eq
        have hx0_3' : s3.readReg64 (.gpr 0#5) = 1#64 := hx0_3
        wp_steps 3
        refine SepWP.weaken_pre (by unfold HbParseRoData; sep_entail)
          (parseCmd_storeTag_wp hcP hlr0 wp_a (by simp [wp_norm, arm64_norm, hrun3])
            (hf3.of_cpu (close_cpu_step s3)) wp_a rfl (by simp [ParseCmdSlot, hp_eq]) hNext)
      · simp only [hclr_eq, Bool.false_eq_true, ↓reduceIte] at hx0_3 hp_eq
        have hx0_3' : s3.readReg64 (.gpr 0#5) = 0#64 := hx0_3
        wp_steps 1
        refine SepWP.weaken_pre (by unfold HbParseRoData; sep_entail)
          (parseCmd_none_wp hcP hlr0 wp_a (by simp [wp_norm, arm64_norm, hrun3])
            (hf3.of_cpu (close_cpu_step s3)) wp_a hp_eq hNext)

private theorem parseCmd_withCap_wp {Q : Program} {C : HbCliLayout}
    {target ret_pc linePtr outPtr c0 c1 c2 : BitVec 64} {line : List (BitVec 8)}
    {s0 s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hcP : CodeChunks Q (hbParseCommandChunks C)) (hcS : CodeChunks Q (hbStripPrefixChunks C))
    (hcB : CodeChunks Q (hbBytesEqChunks C)) (hcD : CodeChunks Q (hbParseDecimalU64Chunks C))
    (hlr0 : s0.readReg64 Reg.lr = ret_pc)
    (hptr_nz : linePtr ≠ 0#64) (hptr_fit : linePtr.toNat + line.length < 2 ^ 64)
    (h1 : stripBytePrefix pfxInsertBytes line = none)
    (h2 : stripBytePrefix pfxRemoveBytes line = none)
    (h3 : stripBytePrefix pfxGetBytes line = none)
    (h4 : stripBytePrefix pfxContainsBytes line = none)
    (hpc : s.pc = C.parseCommandAddr + 0xfc#64) (hrun : s.status = .Running)
    (hf : ParseCmdFrame s0 s) (hx19 : s.readReg64 .x19 = outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 line.length) (hx21 : s.readReg64 .x21 = linePtr)
    (hNext : ∀ (sf : State) (r0' r1' r2' : BitVec 64),
      ParseCmdSlot (parseCommand line) r0' r1' r2' →
      sf.pc = ret_pc → sf.status = .Running → PureCpuStep s0 sf →
      SepWP Q target sf
        ((linePtr ↦ₛ line) ∗ (outPtr ↦₆₄ r0') ∗ ((outPtr + 8#64) ↦₆₄ r1') ∗
         ((outPtr + 16#64) ↦₆₄ r2') ∗ HbParseRoData C ∗ stackAt s0.sp 128 ∗ F) post) :
    SepWP Q target s
      ((linePtr ↦ₛ line) ∗ (outPtr ↦₆₄ c0) ∗ ((outPtr + 8#64) ↦₆₄ c1) ∗
       ((outPtr + 16#64) ↦₆₄ c2) ∗ HbParseRoData C ∗
       parseCmdSavedRegs s0.sp s0 ∗ memRegion (s0.sp - 80#64) 32 ∗
       stackAt (s0.sp - 80#64) 48 ∗ F) post := by
  have hlen : line.length < 2 ^ 64 := by omega
  have hsp_eq := hf.1; have hsp_al := hf.2.1
  unpack_cmd_code hbParseCommandChunks hcP
  wp_steps 1; wp_steps 1; wp_steps 3; wp_steps 1; norm_jmp
  dsimp only [HbParseRoData]
  refine SepWP.weaken_pre (by sep_frame)
    (hbStripPrefix_wp hcS hcB (sp0 := s0.sp - 80#64) (pfx := pfxWithCapBytes)
      (ret_pc := C.parseCommandAddr + 0x114#64)
      hptr_nz hptr_fit (by decide) wp_a (by simp [wp_norm, arm64_norm, hrun])
      (by simp [wp_norm, arm64_norm, hsp_eq])
      (by simp only [State.spAligned, wp_norm, arm64_norm]; simpa [State.spAligned] using hsp_al)
      wp_a wp_a wp_a wp_a rfl
      (fun s1 rest h5 hpc1 hrun1 hcpu1 hx0_1 hr_nz hx1_1 => ?_)
      (fun s1 h5 hpc1 hrun1 hcpu1 hx0_1 => ?_))
  · have hf1 : ParseCmdFrame s0 s1 := hf.of_cpu (PureCpuStep.trans (close_cpu_step s) hcpu1)
    have hx19_1 : s1.readReg64 .x19 = outPtr := hcpu1.2.2.2.2.readReg64_x19.trans wp_a
    have hline_eq := stripBytePrefix_eq_some_iff.mp h5
    have hr_len : rest.length < 2 ^ 64 := by
      have := hptr_fit; rw [hline_eq, List.length_append] at this; omega
    have hcbz : (linePtr + 14#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hr_nz
    wp_steps 1; wp_steps 1; norm_jmp
    conv => arg 4; rw [hline_eq, pointsToBytes_append]
    refine SepWP.weaken_pre (by sep_frame)
      (hbParseDecimalU64_wp hcD (bs := rest)
        (ptr := linePtr + BitVec.ofNat 64 pfxWithCapBytes.length)
        (ret_pc := C.parseCommandAddr + 0x11c#64) hr_len wp_a
        (by simp [wp_norm, arm64_norm, hrun1]) wp_a wp_a wp_a
        (fun s2 cap hdec hpc2 hrun2 hcpu2 hx0_2 hx1_2 => ?_)
        (fun s2 hdec hpc2 hrun2 hcpu2 hx0_2 => ?_))
    · have hf2 : ParseCmdFrame s0 s2 := hf1.of_cpu (PureCpuStep.trans (close_cpu_step s1) hcpu2)
      have hx19_2 : s2.readReg64 .x19 = outPtr := hcpu2.2.2.2.2.readReg64_x19.trans hx19_1
      have hx0_2' : s2.readReg64 (.gpr 0#5) = 1#64 := hx0_2
      have hx1_2' : s2.readReg64 (.gpr 1#5) = cap := hx1_2
      by_cases hcap : cap.toNat ≤ MaxWithCapacity
      · have hult : BitVec.ult 0x1000#64 cap = false := by
          rw [BitVec.ult, show (0x1000#64 : BitVec 64).toNat = MaxWithCapacity from rfl]
          exact decide_eq_false (by omega)
        have hule : BitVec.ule cap 0x1000#64 = true := by
          rw [BitVec.ule, show (0x1000#64 : BitVec 64).toNat = MaxWithCapacity from rfl]
          exact decide_eq_true hcap
        wp_steps 5
        have hp_eq : parseCommand line = some (.withCapacity cap) := by
          rw [parseCommand_of_withCap_pfx h1 h2 h3 h4 h5, hdec]; simp [hcap]
        refine SepWP.weaken_pre
            (by rw [hline_eq, pointsToBytes_append]; unfold HbParseRoData; sep_entail)
          (parseCmd_storePair_wp (tag := 4#64) (val := cap) hcP hlr0 wp_a
            (by simp [wp_norm, arm64_norm, hrun2])
            (hf2.of_cpu (close_cpu_step s2)) wp_a rfl
            (by simp [wp_norm, arm64_norm, hx1_2])
            (by simp [ParseCmdSlot, hp_eq, hcap]) hNext)
      · have hult : BitVec.ult 0x1000#64 cap = true := by
          rw [BitVec.ult, show (0x1000#64 : BitVec 64).toNat = MaxWithCapacity from rfl]
          exact decide_eq_true (by omega)
        have hule : BitVec.ule cap 0x1000#64 = false := by
          rw [BitVec.ule, show (0x1000#64 : BitVec 64).toNat = MaxWithCapacity from rfl]
          exact decide_eq_false hcap
        wp_steps 3
        have hp_eq : parseCommand line = none := by
          rw [parseCommand_of_withCap_pfx h1 h2 h3 h4 h5, hdec]; simp [hcap]
        refine SepWP.weaken_pre
            (by rw [hline_eq, pointsToBytes_append]; unfold HbParseRoData; sep_entail)
          (parseCmd_none_wp hcP hlr0 wp_a (by simp [wp_norm, arm64_norm, hrun2])
            (hf2.of_cpu (close_cpu_step s2)) wp_a hp_eq hNext)
    · have hf2 : ParseCmdFrame s0 s2 := hf1.of_cpu (PureCpuStep.trans (close_cpu_step s1) hcpu2)
      have hx19_2 : s2.readReg64 .x19 = outPtr := hcpu2.2.2.2.2.readReg64_x19.trans hx19_1
      have hx0_2' : s2.readReg64 (.gpr 0#5) = 0#64 := hx0_2
      wp_steps 1
      have hp_eq : parseCommand line = none := by
        rw [parseCommand_of_withCap_pfx h1 h2 h3 h4 h5, hdec]; rfl
      refine SepWP.weaken_pre
          (by rw [hline_eq, pointsToBytes_append]; unfold HbParseRoData; sep_entail)
        (parseCmd_none_wp hcP hlr0 wp_a (by simp [wp_norm, arm64_norm, hrun2])
          (hf2.of_cpu (close_cpu_step s2)) wp_a hp_eq hNext)
  · have hf1 : ParseCmdFrame s0 s1 := hf.of_cpu (PureCpuStep.trans (close_cpu_step s) hcpu1)
    have hx19_1 : s1.readReg64 .x19 = outPtr := hcpu1.2.2.2.2.readReg64_x19.trans wp_a
    have hx20_1 : s1.readReg64 .x20 = BitVec.ofNat 64 line.length :=
      hcpu1.2.2.2.2.readReg64_x20.trans wp_a
    have hx21_1 : s1.readReg64 .x21 = linePtr := hcpu1.2.2.2.2.readReg64_x21.trans wp_a
    have hx0_1' : s1.readReg64 (.gpr 0#5) = 0#64 := hx0_1
    wp_steps 1
    refine SepWP.weaken_pre (by unfold HbParseRoData; sep_entail)
      (parseCmd_exact_wp hcP hcB hlr0 hlen h1 h2 h3 h4 h5
        wp_a (by simp [wp_norm, arm64_norm, hrun1])
        (hf1.of_cpu (close_cpu_step s1)) wp_a wp_a wp_a hNext)

private theorem parseCmd_contains_wp {Q : Program} {C : HbCliLayout}
    {target ret_pc linePtr outPtr c0 c1 c2 : BitVec 64} {line : List (BitVec 8)}
    {s0 s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hcP : CodeChunks Q (hbParseCommandChunks C)) (hcS : CodeChunks Q (hbStripPrefixChunks C))
    (hcB : CodeChunks Q (hbBytesEqChunks C)) (hcD : CodeChunks Q (hbParseDecimalU64Chunks C))
    (hlr0 : s0.readReg64 Reg.lr = ret_pc)
    (hptr_nz : linePtr ≠ 0#64) (hptr_fit : linePtr.toNat + line.length < 2 ^ 64)
    (h1 : stripBytePrefix pfxInsertBytes line = none)
    (h2 : stripBytePrefix pfxRemoveBytes line = none)
    (h3 : stripBytePrefix pfxGetBytes line = none)
    (hpc : s.pc = C.parseCommandAddr + 0xcc#64) (hrun : s.status = .Running)
    (hf : ParseCmdFrame s0 s) (hx19 : s.readReg64 .x19 = outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 line.length) (hx21 : s.readReg64 .x21 = linePtr)
    (hNext : ∀ (sf : State) (r0' r1' r2' : BitVec 64),
      ParseCmdSlot (parseCommand line) r0' r1' r2' →
      sf.pc = ret_pc → sf.status = .Running → PureCpuStep s0 sf →
      SepWP Q target sf
        ((linePtr ↦ₛ line) ∗ (outPtr ↦₆₄ r0') ∗ ((outPtr + 8#64) ↦₆₄ r1') ∗
         ((outPtr + 16#64) ↦₆₄ r2') ∗ HbParseRoData C ∗ stackAt s0.sp 128 ∗ F) post) :
    SepWP Q target s
      ((linePtr ↦ₛ line) ∗ (outPtr ↦₆₄ c0) ∗ ((outPtr + 8#64) ↦₆₄ c1) ∗
       ((outPtr + 16#64) ↦₆₄ c2) ∗ HbParseRoData C ∗
       parseCmdSavedRegs s0.sp s0 ∗ memRegion (s0.sp - 80#64) 32 ∗
       stackAt (s0.sp - 80#64) 48 ∗ F) post := by
  have hsp_eq := hf.1; have hsp_al := hf.2.1
  unpack_cmd_code hbParseCommandChunks hcP
  wp_steps 1; wp_steps 1; wp_steps 3; wp_steps 1; norm_jmp
  dsimp only [HbParseRoData]
  refine SepWP.weaken_pre (by sep_frame)
    (hbStripPrefix_wp hcS hcB (sp0 := s0.sp - 80#64) (pfx := pfxContainsBytes)
      (ret_pc := C.parseCommandAddr + 0xe4#64)
      hptr_nz hptr_fit (by decide) wp_a (by simp [wp_norm, arm64_norm, hrun])
      (by simp [wp_norm, arm64_norm, hsp_eq])
      (by simp only [State.spAligned, wp_norm, arm64_norm]; simpa [State.spAligned] using hsp_al)
      wp_a wp_a wp_a wp_a rfl
      (fun s1 rest h4 hpc1 hrun1 hcpu1 hx0_1 hr_nz hx1_1 => ?_)
      (fun s1 h4 hpc1 hrun1 hcpu1 hx0_1 => ?_))
  · have hf1 : ParseCmdFrame s0 s1 := hf.of_cpu (PureCpuStep.trans (close_cpu_step s) hcpu1)
    have hx19_1 : s1.readReg64 .x19 = outPtr := hcpu1.2.2.2.2.readReg64_x19.trans wp_a
    have hline_eq := stripBytePrefix_eq_some_iff.mp h4
    have hr_len : rest.length < 2 ^ 64 := by
      have := hptr_fit; rw [hline_eq, List.length_append] at this; omega
    have hcbz : (linePtr + 9#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hr_nz
    wp_steps 1; wp_steps 1; norm_jmp
    conv => arg 4; rw [hline_eq, pointsToBytes_append]
    refine SepWP.weaken_pre (by sep_frame)
      (hbParseDecimalU64_wp hcD (bs := rest)
        (ptr := linePtr + BitVec.ofNat 64 pfxContainsBytes.length)
        (ret_pc := C.parseCommandAddr + 0xec#64) hr_len wp_a
        (by simp [wp_norm, arm64_norm, hrun1]) wp_a wp_a wp_a
        (fun s2 v hdec hpc2 hrun2 hcpu2 hx0_2 hx1_2 => ?_)
        (fun s2 hdec hpc2 hrun2 hcpu2 hx0_2 => ?_))
    · have hf2 : ParseCmdFrame s0 s2 := hf1.of_cpu (PureCpuStep.trans (close_cpu_step s1) hcpu2)
      have hx19_2 : s2.readReg64 .x19 = outPtr := hcpu2.2.2.2.2.readReg64_x19.trans hx19_1
      have hx0_2' : s2.readReg64 (.gpr 0#5) = 1#64 := hx0_2
      wp_steps 2
      have hp_eq : parseCommand line = some (.contains v) := by
        rw [parseCommand_of_contains_pfx h1 h2 h3 h4, hdec]; rfl
      refine SepWP.weaken_pre
          (by rw [hline_eq, pointsToBytes_append]; unfold HbParseRoData; sep_entail)
        (parseCmd_storePair_wp (tag := 3#64) (val := v) hcP hlr0 wp_a
          (by simp [wp_norm, arm64_norm, hrun2])
          (hf2.of_cpu (close_cpu_step s2)) wp_a rfl
          (by simp [wp_norm, arm64_norm, hx1_2])
          (by simp [ParseCmdSlot, hp_eq]) hNext)
    · have hf2 : ParseCmdFrame s0 s2 := hf1.of_cpu (PureCpuStep.trans (close_cpu_step s1) hcpu2)
      have hx19_2 : s2.readReg64 .x19 = outPtr := hcpu2.2.2.2.2.readReg64_x19.trans hx19_1
      have hx0_2' : s2.readReg64 (.gpr 0#5) = 0#64 := hx0_2
      wp_steps 1
      have hp_eq : parseCommand line = none := by
        rw [parseCommand_of_contains_pfx h1 h2 h3 h4, hdec]; rfl
      refine SepWP.weaken_pre
          (by rw [hline_eq, pointsToBytes_append]; unfold HbParseRoData; sep_entail)
        (parseCmd_none_wp hcP hlr0 wp_a (by simp [wp_norm, arm64_norm, hrun2])
          (hf2.of_cpu (close_cpu_step s2)) wp_a hp_eq hNext)
  · have hf1 : ParseCmdFrame s0 s1 := hf.of_cpu (PureCpuStep.trans (close_cpu_step s) hcpu1)
    have hx19_1 : s1.readReg64 .x19 = outPtr := hcpu1.2.2.2.2.readReg64_x19.trans wp_a
    have hx20_1 : s1.readReg64 .x20 = BitVec.ofNat 64 line.length :=
      hcpu1.2.2.2.2.readReg64_x20.trans wp_a
    have hx21_1 : s1.readReg64 .x21 = linePtr := hcpu1.2.2.2.2.readReg64_x21.trans wp_a
    have hx0_1' : s1.readReg64 (.gpr 0#5) = 0#64 := hx0_1
    wp_steps 1
    refine SepWP.weaken_pre (by unfold HbParseRoData; sep_entail)
      (parseCmd_withCap_wp hcP hcS hcB hcD hlr0 hptr_nz hptr_fit h1 h2 h3 h4
        wp_a (by simp [wp_norm, arm64_norm, hrun1])
        (hf1.of_cpu (close_cpu_step s1)) wp_a wp_a wp_a hNext)

private theorem parseCmd_get_wp {Q : Program} {C : HbCliLayout}
    {target ret_pc linePtr outPtr c0 c1 c2 : BitVec 64} {line : List (BitVec 8)}
    {s0 s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hcP : CodeChunks Q (hbParseCommandChunks C)) (hcS : CodeChunks Q (hbStripPrefixChunks C))
    (hcB : CodeChunks Q (hbBytesEqChunks C)) (hcD : CodeChunks Q (hbParseDecimalU64Chunks C))
    (hlr0 : s0.readReg64 Reg.lr = ret_pc)
    (hptr_nz : linePtr ≠ 0#64) (hptr_fit : linePtr.toNat + line.length < 2 ^ 64)
    (h1 : stripBytePrefix pfxInsertBytes line = none)
    (h2 : stripBytePrefix pfxRemoveBytes line = none)
    (hpc : s.pc = C.parseCommandAddr + 0xa0#64) (hrun : s.status = .Running)
    (hf : ParseCmdFrame s0 s) (hx19 : s.readReg64 .x19 = outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 line.length) (hx21 : s.readReg64 .x21 = linePtr)
    (hNext : ∀ (sf : State) (r0' r1' r2' : BitVec 64),
      ParseCmdSlot (parseCommand line) r0' r1' r2' →
      sf.pc = ret_pc → sf.status = .Running → PureCpuStep s0 sf →
      SepWP Q target sf
        ((linePtr ↦ₛ line) ∗ (outPtr ↦₆₄ r0') ∗ ((outPtr + 8#64) ↦₆₄ r1') ∗
         ((outPtr + 16#64) ↦₆₄ r2') ∗ HbParseRoData C ∗ stackAt s0.sp 128 ∗ F) post) :
    SepWP Q target s
      ((linePtr ↦ₛ line) ∗ (outPtr ↦₆₄ c0) ∗ ((outPtr + 8#64) ↦₆₄ c1) ∗
       ((outPtr + 16#64) ↦₆₄ c2) ∗ HbParseRoData C ∗
       parseCmdSavedRegs s0.sp s0 ∗ memRegion (s0.sp - 80#64) 32 ∗
       stackAt (s0.sp - 80#64) 48 ∗ F) post := by
  have hsp_eq := hf.1; have hsp_al := hf.2.1
  unpack_cmd_code hbParseCommandChunks hcP
  wp_steps 1; wp_steps 1; wp_steps 3; wp_steps 1; norm_jmp
  dsimp only [HbParseRoData]
  refine SepWP.weaken_pre (by sep_frame)
    (hbStripPrefix_wp hcS hcB (sp0 := s0.sp - 80#64) (pfx := pfxGetBytes)
      (ret_pc := C.parseCommandAddr + 0xb8#64)
      hptr_nz hptr_fit (by decide) wp_a (by simp [wp_norm, arm64_norm, hrun])
      (by simp [wp_norm, arm64_norm, hsp_eq])
      (by simp only [State.spAligned, wp_norm, arm64_norm]; simpa [State.spAligned] using hsp_al)
      wp_a wp_a wp_a wp_a rfl
      (fun s1 rest h3 hpc1 hrun1 hcpu1 hx0_1 hr_nz hx1_1 => ?_)
      (fun s1 h3 hpc1 hrun1 hcpu1 hx0_1 => ?_))
  · have hf1 : ParseCmdFrame s0 s1 := hf.of_cpu (PureCpuStep.trans (close_cpu_step s) hcpu1)
    have hx19_1 : s1.readReg64 .x19 = outPtr := hcpu1.2.2.2.2.readReg64_x19.trans wp_a
    have hline_eq := stripBytePrefix_eq_some_iff.mp h3
    have hr_len : rest.length < 2 ^ 64 := by
      have := hptr_fit; rw [hline_eq, List.length_append] at this; omega
    have hcbz : (linePtr + 4#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hr_nz
    wp_steps 1; wp_steps 1; norm_jmp
    conv => arg 4; rw [hline_eq, pointsToBytes_append]
    refine SepWP.weaken_pre (by sep_frame)
      (hbParseDecimalU64_wp hcD (bs := rest)
        (ptr := linePtr + BitVec.ofNat 64 pfxGetBytes.length)
        (ret_pc := C.parseCommandAddr + 0xc0#64) hr_len wp_a
        (by simp [wp_norm, arm64_norm, hrun1]) wp_a wp_a wp_a
        (fun s2 v hdec hpc2 hrun2 hcpu2 hx0_2 hx1_2 => ?_)
        (fun s2 hdec hpc2 hrun2 hcpu2 hx0_2 => ?_))
    · have hf2 : ParseCmdFrame s0 s2 := hf1.of_cpu (PureCpuStep.trans (close_cpu_step s1) hcpu2)
      have hx19_2 : s2.readReg64 .x19 = outPtr := hcpu2.2.2.2.2.readReg64_x19.trans hx19_1
      have hx0_2' : s2.readReg64 (.gpr 0#5) = 1#64 := hx0_2
      wp_steps 3
      have hp_eq : parseCommand line = some (.get v) := by
        rw [parseCommand_of_get_pfx h1 h2 h3, hdec]; rfl
      refine SepWP.weaken_pre
          (by rw [hline_eq, pointsToBytes_append]; unfold HbParseRoData; sep_entail)
        (parseCmd_storePair_wp (tag := 1#64) (val := v) hcP hlr0 wp_a
          (by simp [wp_norm, arm64_norm, hrun2])
          (hf2.of_cpu (close_cpu_step s2)) wp_a rfl
          (by simp [wp_norm, arm64_norm, hx1_2])
          (by simp [ParseCmdSlot, hp_eq]) hNext)
    · have hf2 : ParseCmdFrame s0 s2 := hf1.of_cpu (PureCpuStep.trans (close_cpu_step s1) hcpu2)
      have hx19_2 : s2.readReg64 .x19 = outPtr := hcpu2.2.2.2.2.readReg64_x19.trans hx19_1
      have hx0_2' : s2.readReg64 (.gpr 0#5) = 0#64 := hx0_2
      wp_steps 1
      have hp_eq : parseCommand line = none := by
        rw [parseCommand_of_get_pfx h1 h2 h3, hdec]; rfl
      refine SepWP.weaken_pre
          (by rw [hline_eq, pointsToBytes_append]; unfold HbParseRoData; sep_entail)
        (parseCmd_none_wp hcP hlr0 wp_a (by simp [wp_norm, arm64_norm, hrun2])
          (hf2.of_cpu (close_cpu_step s2)) wp_a hp_eq hNext)
  · have hf1 : ParseCmdFrame s0 s1 := hf.of_cpu (PureCpuStep.trans (close_cpu_step s) hcpu1)
    have hx19_1 : s1.readReg64 .x19 = outPtr := hcpu1.2.2.2.2.readReg64_x19.trans wp_a
    have hx20_1 : s1.readReg64 .x20 = BitVec.ofNat 64 line.length :=
      hcpu1.2.2.2.2.readReg64_x20.trans wp_a
    have hx21_1 : s1.readReg64 .x21 = linePtr := hcpu1.2.2.2.2.readReg64_x21.trans wp_a
    have hx0_1' : s1.readReg64 (.gpr 0#5) = 0#64 := hx0_1
    wp_steps 1
    refine SepWP.weaken_pre (by unfold HbParseRoData; sep_entail)
      (parseCmd_contains_wp hcP hcS hcB hcD hlr0 hptr_nz hptr_fit h1 h2 h3
        wp_a (by simp [wp_norm, arm64_norm, hrun1])
        (hf1.of_cpu (close_cpu_step s1)) wp_a wp_a wp_a hNext)

private theorem parseCmd_from0x74_wp {Q : Program} {C : HbCliLayout}
    {target ret_pc linePtr outPtr c0 c1 c2 : BitVec 64} {line : List (BitVec 8)}
    {s0 s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hcP : CodeChunks Q (hbParseCommandChunks C)) (hcS : CodeChunks Q (hbStripPrefixChunks C))
    (hcB : CodeChunks Q (hbBytesEqChunks C)) (hcD : CodeChunks Q (hbParseDecimalU64Chunks C))
    (hlr0 : s0.readReg64 Reg.lr = ret_pc)
    (hptr_nz : linePtr ≠ 0#64) (hptr_fit : linePtr.toNat + line.length < 2 ^ 64)
    (h1 : stripBytePrefix pfxInsertBytes line = none)
    (hpc : s.pc = C.parseCommandAddr + 0x74#64) (hrun : s.status = .Running)
    (hf : ParseCmdFrame s0 s) (hx19 : s.readReg64 .x19 = outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 line.length) (hx21 : s.readReg64 .x21 = linePtr)
    (hNext : ∀ (sf : State) (r0' r1' r2' : BitVec 64),
      ParseCmdSlot (parseCommand line) r0' r1' r2' →
      sf.pc = ret_pc → sf.status = .Running → PureCpuStep s0 sf →
      SepWP Q target sf
        ((linePtr ↦ₛ line) ∗ (outPtr ↦₆₄ r0') ∗ ((outPtr + 8#64) ↦₆₄ r1') ∗
         ((outPtr + 16#64) ↦₆₄ r2') ∗ HbParseRoData C ∗ stackAt s0.sp 128 ∗ F) post) :
    SepWP Q target s
      ((linePtr ↦ₛ line) ∗ (outPtr ↦₆₄ c0) ∗ ((outPtr + 8#64) ↦₆₄ c1) ∗
       ((outPtr + 16#64) ↦₆₄ c2) ∗ HbParseRoData C ∗
       parseCmdSavedRegs s0.sp s0 ∗ memRegion (s0.sp - 80#64) 32 ∗
       stackAt (s0.sp - 80#64) 48 ∗ F) post := by
  have hsp_eq := hf.1; have hsp_al := hf.2.1
  unpack_cmd_code hbParseCommandChunks hcP
  wp_steps 1; wp_steps 1; wp_steps 3; wp_steps 1; norm_jmp
  dsimp only [HbParseRoData]
  refine SepWP.weaken_pre (by sep_frame)
    (hbStripPrefix_wp hcS hcB (sp0 := s0.sp - 80#64) (pfx := pfxRemoveBytes)
      (ret_pc := C.parseCommandAddr + 0x8c#64)
      hptr_nz hptr_fit (by decide) wp_a (by simp [wp_norm, arm64_norm, hrun])
      (by simp [wp_norm, arm64_norm, hsp_eq])
      (by simp only [State.spAligned, wp_norm, arm64_norm]; simpa [State.spAligned] using hsp_al)
      wp_a wp_a wp_a wp_a rfl
      (fun s1 rest h2 hpc1 hrun1 hcpu1 hx0_1 hr_nz hx1_1 => ?_)
      (fun s1 h2 hpc1 hrun1 hcpu1 hx0_1 => ?_))
  · have hf1 : ParseCmdFrame s0 s1 := hf.of_cpu (PureCpuStep.trans (close_cpu_step s) hcpu1)
    have hx19_1 : s1.readReg64 .x19 = outPtr := hcpu1.2.2.2.2.readReg64_x19.trans wp_a
    have hline_eq := stripBytePrefix_eq_some_iff.mp h2
    have hr_len : rest.length < 2 ^ 64 := by
      have := hptr_fit; rw [hline_eq, List.length_append] at this; omega
    have hcbz : (linePtr + 7#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hr_nz
    wp_steps 1; wp_steps 1; norm_jmp
    conv => arg 4; rw [hline_eq, pointsToBytes_append]
    refine SepWP.weaken_pre (by sep_frame)
      (hbParseDecimalU64_wp hcD (bs := rest)
        (ptr := linePtr + BitVec.ofNat 64 pfxRemoveBytes.length)
        (ret_pc := C.parseCommandAddr + 0x94#64) hr_len wp_a
        (by simp [wp_norm, arm64_norm, hrun1]) wp_a wp_a wp_a
        (fun s2 v hdec hpc2 hrun2 hcpu2 hx0_2 hx1_2 => ?_)
        (fun s2 hdec hpc2 hrun2 hcpu2 hx0_2 => ?_))
    · have hf2 : ParseCmdFrame s0 s2 := hf1.of_cpu (PureCpuStep.trans (close_cpu_step s1) hcpu2)
      have hx19_2 : s2.readReg64 .x19 = outPtr := hcpu2.2.2.2.2.readReg64_x19.trans hx19_1
      have hx0_2' : s2.readReg64 (.gpr 0#5) = 1#64 := hx0_2
      wp_steps 3
      have hp_eq : parseCommand line = some (.remove v) := by
        rw [parseCommand_of_remove_pfx h1 h2, hdec]; rfl
      refine SepWP.weaken_pre
          (by rw [hline_eq, pointsToBytes_append]; unfold HbParseRoData; sep_entail)
        (parseCmd_storePair_wp (tag := 2#64) (val := v) hcP hlr0 wp_a
          (by simp [wp_norm, arm64_norm, hrun2])
          (hf2.of_cpu (close_cpu_step s2)) wp_a rfl
          (by simp [wp_norm, arm64_norm, hx1_2])
          (by simp [ParseCmdSlot, hp_eq]) hNext)
    · have hf2 : ParseCmdFrame s0 s2 := hf1.of_cpu (PureCpuStep.trans (close_cpu_step s1) hcpu2)
      have hx19_2 : s2.readReg64 .x19 = outPtr := hcpu2.2.2.2.2.readReg64_x19.trans hx19_1
      have hx0_2' : s2.readReg64 (.gpr 0#5) = 0#64 := hx0_2
      wp_steps 1
      have hp_eq : parseCommand line = none := by
        rw [parseCommand_of_remove_pfx h1 h2, hdec]; rfl
      refine SepWP.weaken_pre
          (by rw [hline_eq, pointsToBytes_append]; unfold HbParseRoData; sep_entail)
        (parseCmd_none_wp hcP hlr0 wp_a (by simp [wp_norm, arm64_norm, hrun2])
          (hf2.of_cpu (close_cpu_step s2)) wp_a hp_eq hNext)
  · have hf1 : ParseCmdFrame s0 s1 := hf.of_cpu (PureCpuStep.trans (close_cpu_step s) hcpu1)
    have hx19_1 : s1.readReg64 .x19 = outPtr := hcpu1.2.2.2.2.readReg64_x19.trans wp_a
    have hx20_1 : s1.readReg64 .x20 = BitVec.ofNat 64 line.length :=
      hcpu1.2.2.2.2.readReg64_x20.trans wp_a
    have hx21_1 : s1.readReg64 .x21 = linePtr := hcpu1.2.2.2.2.readReg64_x21.trans wp_a
    have hx0_1' : s1.readReg64 (.gpr 0#5) = 0#64 := hx0_1
    wp_steps 1
    refine SepWP.weaken_pre (by unfold HbParseRoData; sep_entail)
      (parseCmd_get_wp hcP hcS hcB hcD hlr0 hptr_nz hptr_fit h1 h2
        wp_a (by simp [wp_norm, arm64_norm, hrun1])
        (hf1.of_cpu (close_cpu_step s1)) wp_a wp_a wp_a hNext)

private theorem parseCmd_insertRest_wp {Q : Program} {C : HbCliLayout}
    {target ret_pc linePtr outPtr c0 c1 c2 : BitVec 64} {line rest : List (BitVec 8)}
    {s0 s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hcP : CodeChunks Q (hbParseCommandChunks C))
    (hcSp : CodeChunks Q (hbSplitOnceSpaceChunks C))
    (hcD : CodeChunks Q (hbParseDecimalU64Chunks C))
    (hlr0 : s0.readReg64 Reg.lr = ret_pc)
    (hptr_fit : linePtr.toNat + line.length < 2 ^ 64)
    (h1 : stripBytePrefix pfxInsertBytes line = some rest)
    (hr_nz : linePtr + BitVec.ofNat 64 pfxInsertBytes.length ≠ 0#64)
    (hpc : s.pc = C.parseCommandAddr + 0x30#64) (hrun : s.status = .Running)
    (hf : ParseCmdFrame s0 s) (hx19 : s.readReg64 .x19 = outPtr)
    (hx0 : s.readReg64 .x0 = linePtr + BitVec.ofNat 64 pfxInsertBytes.length)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 rest.length)
    (hNext : ∀ (sf : State) (r0' r1' r2' : BitVec 64),
      ParseCmdSlot (parseCommand line) r0' r1' r2' →
      sf.pc = ret_pc → sf.status = .Running → PureCpuStep s0 sf →
      SepWP Q target sf
        ((linePtr ↦ₛ line) ∗ (outPtr ↦₆₄ r0') ∗ ((outPtr + 8#64) ↦₆₄ r1') ∗
         ((outPtr + 16#64) ↦₆₄ r2') ∗ HbParseRoData C ∗ stackAt s0.sp 128 ∗ F) post) :
    SepWP Q target s
      ((linePtr ↦ₛ line) ∗ (outPtr ↦₆₄ c0) ∗ ((outPtr + 8#64) ↦₆₄ c1) ∗
       ((outPtr + 16#64) ↦₆₄ c2) ∗ HbParseRoData C ∗
       parseCmdSavedRegs s0.sp s0 ∗ memRegion (s0.sp - 80#64) 32 ∗
       stackAt (s0.sp - 80#64) 48 ∗ F) post := by
  have hsp_eq := hf.1
  have hline_eq := stripBytePrefix_eq_some_iff.mp h1
  have hl_add : line.length = 7 + rest.length := by
    rw [hline_eq, List.length_append]; rfl
  have hr_fit : (linePtr + BitVec.ofNat 64 pfxInsertBytes.length).toNat + rest.length < 2 ^ 64 := by
    rw [BitVec.toNat_add, show (BitVec.ofNat 64 pfxInsertBytes.length).toNat = 7 from rfl,
        Nat.mod_eq_of_lt (by omega)]
    omega
  have hcbz : (linePtr + BitVec.ofNat 64 pfxInsertBytes.length == 0#64) = false :=
    beq_eq_false_iff_ne.mpr hr_nz
  have hcbz7 : (linePtr + 7#64 == 0#64) = false := hcbz
  unpack_cmd_code hbParseCommandChunks hcP
  wp_steps 2; wp_steps 1; norm_jmp
  conv => arg 4; rw [hline_eq, pointsToBytes_append]
  refine SepWP.weaken_pre (by sep_frame)
    (hbSplitOnceSpace_wp hcSp (rest := rest)
      (restPtr := linePtr + BitVec.ofNat 64 pfxInsertBytes.length)
      (outPtr := s0.sp - 80#64) (ret_pc := C.parseCommandAddr + 0x3c#64)
      hr_nz hr_fit wp_a (by simp [wp_norm, arm64_norm, hrun]) wp_a wp_a wp_a wp_a
      (fun s2 k hk hsp_some hpc2 hrun2 hcpu2 => ?_)
      (fun s2 hsp_none hpc2 hrun2 hcpu2 => ?_))
  · have hf2 : ParseCmdFrame s0 s2 := hf.of_cpu (PureCpuStep.trans (close_cpu_step s) hcpu2)
    have hsp2 : s2.sp = s0.sp - 80#64 := hf2.1
    have hsp2_al : s2.spAligned = true := hf2.2.1
    have hx19_2 : s2.readReg64 (.gpr 19#5) = outPtr := hcpu2.2.2.2.2.readReg64_x19.trans wp_a
    have hkle : k ≤ rest.length := by omega
    have htake_k : (rest.take k).length = k := List.length_take_of_le hkle
    wp_steps 4; wp_steps 1; norm_jmp
    conv => arg 4; rw [pointsToBytes_take_drop _ k rest hkle]
    refine SepWP.weaken_pre (by sep_frame)
      (hbParseDecimalU64_wp hcD (bs := rest.take k)
        (ptr := linePtr + BitVec.ofNat 64 pfxInsertBytes.length)
        (ret_pc := C.parseCommandAddr + 0x50#64) (by rw [htake_k]; omega)
        wp_a (by simp [wp_norm, arm64_norm, hrun2]) wp_a wp_a
        (by simp [wp_norm, arm64_norm, htake_k])
        (fun s3 kval hk_some hpc3 hrun3 hcpu3 hx0_3 hx1_3 => ?_)
        (fun s3 hk_none hpc3 hrun3 hcpu3 hx0_3 => ?_))
    · have hf3 : ParseCmdFrame s0 s3 := (close_parse_frame hf2).of_cpu hcpu3
      have hx19_3 : s3.readReg64 .x19 = outPtr :=
        hcpu3.2.2.2.2.readReg64_x19.trans (by simp [wp_norm, arm64_norm] at hx19_2 ⊢; exact hx19_2)
      have hx21_3 : s3.readReg64 .x21 =
          linePtr + BitVec.ofNat 64 pfxInsertBytes.length + BitVec.ofNat 64 (k + 1) :=
        hcpu3.2.2.2.2.readReg64_x21.trans wp_a
      have hx22_3 : s3.readReg64 .x22 = BitVec.ofNat 64 (rest.drop (k + 1)).length :=
        hcpu3.2.2.2.2.readReg64_x22.trans wp_a
      have hx0_3' : s3.readReg64 (.gpr 0#5) = 1#64 := hx0_3
      have hx1_3' : s3.readReg64 (.gpr 1#5) = kval := hx1_3
      have hk1le : k + 1 ≤ rest.length := hk
      wp_steps 4; wp_steps 1; norm_jmp
      conv => arg 4; rw [← sepConj_assoc, ← pointsToBytes_take_drop _ k rest hkle,
                         pointsToBytes_take_drop _ (k + 1) rest hk1le, sepConj_assoc]
      refine SepWP.weaken_pre (by sep_frame)
        (hbParseDecimalU64_wp hcD (bs := rest.drop (k + 1))
          (ptr := linePtr + BitVec.ofNat 64 pfxInsertBytes.length + BitVec.ofNat 64 (k + 1))
          (ret_pc := C.parseCommandAddr + 0x64#64) (by rw [List.length_drop]; omega)
          wp_a (by simp [wp_norm, arm64_norm, hrun3]) wp_a wp_a wp_a
          (fun s4 vval hv_some hpc4 hrun4 hcpu4 hx0_4 hx1_4 => ?_)
          (fun s4 hv_none hpc4 hrun4 hcpu4 hx0_4 => ?_))
      · have hf4 : ParseCmdFrame s0 s4 := (close_parse_frame hf3).of_cpu hcpu4
        have hx19_4 : s4.readReg64 (.gpr 19#5) = outPtr :=
          hcpu4.2.2.2.2.readReg64_x19.trans hx19_3
        have hx20_4 : s4.readReg64 (.gpr 20#5) = kval := hcpu4.2.2.2.2.readReg64_x20.trans wp_a
        have hx0_4' : s4.readReg64 (.gpr 0#5) = 1#64 := hx0_4
        have hx1_4' : s4.readReg64 (.gpr 1#5) = vval := hx1_4
        wp_steps 4
        have hp_eq : parseCommand line = some (.insert kval vval) := by
          rw [parseCommand_of_insert_pfx h1, hsp_some]; simp [hk_some, hv_some]
        have hc4 := cells4_to_memRegion32 (s0.sp - 80#64)
          (linePtr + BitVec.ofNat 64 pfxInsertBytes.length) (BitVec.ofNat 64 k)
          (linePtr + BitVec.ofNat 64 pfxInsertBytes.length + BitVec.ofNat 64 (k + 1))
          (BitVec.ofNat 64 (rest.drop (k + 1)).length)
        refine SepWP.weaken_pre ?_
          (parseCmd_epilogue_wp hcP hlr0 (r0 := 0#64) (r1 := kval) (r2 := vval)
            wp_a (by simp [wp_norm, arm64_norm, hrun4])
            (hf4.of_cpu (close_cpu_step s4)) (by simp [ParseCmdSlot, hp_eq]) hNext)
        rw [hline_eq, pointsToBytes_append, pointsToBytes_take_drop _ (k + 1) rest hk1le]
        refine Entails.trans ?_
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hc4)))))))
        sep_entail
      · have hf4 : ParseCmdFrame s0 s4 := (close_parse_frame hf3).of_cpu hcpu4
        have hx19_4 : s4.readReg64 .x19 = outPtr :=
          hcpu4.2.2.2.2.readReg64_x19.trans hx19_3
        have hx0_4' : s4.readReg64 (.gpr 0#5) = 0#64 := hx0_4
        wp_steps 1
        have hp_eq : parseCommand line = none := by
          rw [parseCommand_of_insert_pfx h1, hsp_some]; simp [hk_some, hv_none]
        have hc4 := cells4_to_memRegion32 (s0.sp - 80#64)
          (linePtr + BitVec.ofNat 64 pfxInsertBytes.length) (BitVec.ofNat 64 k)
          (linePtr + BitVec.ofNat 64 pfxInsertBytes.length + BitVec.ofNat 64 (k + 1))
          (BitVec.ofNat 64 (rest.drop (k + 1)).length)
        refine SepWP.weaken_pre ?_
          (parseCmd_none_wp hcP hlr0 (c0 := c0) (c1 := c1) (c2 := c2)
            wp_a (by simp [wp_norm, arm64_norm, hrun4])
            (hf4.of_cpu (close_cpu_step s4))
            (by simp [wp_norm, arm64_norm] at hx19_4 ⊢; exact hx19_4) hp_eq hNext)
        rw [hline_eq, pointsToBytes_append, pointsToBytes_take_drop _ (k + 1) rest hk1le]
        refine Entails.trans ?_
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hc4)))))))
        sep_entail
    · have hf3 : ParseCmdFrame s0 s3 := (close_parse_frame hf2).of_cpu hcpu3
      have hx19_3 : s3.readReg64 .x19 = outPtr :=
        hcpu3.2.2.2.2.readReg64_x19.trans (by simp [wp_norm, arm64_norm] at hx19_2 ⊢; exact hx19_2)
      have hx0_3' : s3.readReg64 (.gpr 0#5) = 0#64 := hx0_3
      wp_steps 1
      have hp_eq : parseCommand line = none := by
        rw [parseCommand_of_insert_pfx h1, hsp_some]; simp [hk_none]
      have hc4 := cells4_to_memRegion32 (s0.sp - 80#64)
        (linePtr + BitVec.ofNat 64 pfxInsertBytes.length) (BitVec.ofNat 64 k)
        (linePtr + BitVec.ofNat 64 pfxInsertBytes.length + BitVec.ofNat 64 (k + 1))
        (BitVec.ofNat 64 (rest.drop (k + 1)).length)
      refine SepWP.weaken_pre ?_
        (parseCmd_none_wp hcP hlr0 (c0 := c0) (c1 := c1) (c2 := c2)
          wp_a (by simp [wp_norm, arm64_norm, hrun3])
          (hf3.of_cpu (close_cpu_step s3))
          (by simp [wp_norm, arm64_norm] at hx19_3 ⊢; exact hx19_3) hp_eq hNext)
      rw [hline_eq, pointsToBytes_append, pointsToBytes_take_drop _ k rest hkle]
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hc4)))))))
      sep_entail
  · have hf2 : ParseCmdFrame s0 s2 := hf.of_cpu (PureCpuStep.trans (close_cpu_step s) hcpu2)
    have hsp2 : s2.sp = s0.sp - 80#64 := hf2.1
    have hsp2_al : s2.spAligned = true := hf2.2.1
    have hx19_2 : s2.readReg64 .x19 = outPtr := hcpu2.2.2.2.2.readReg64_x19.trans wp_a
    wp_steps 2
    have hp_eq : parseCommand line = none := by
      rw [parseCommand_of_insert_pfx h1, hsp_none]
    have hc1 := cell_memRegion24_to_32 (s0.sp - 80#64) 0#64
    refine SepWP.weaken_pre ?_
      (parseCmd_none_wp hcP hlr0 (c0 := c0) (c1 := c1) (c2 := c2)
        wp_a (by simp [wp_norm, arm64_norm, hrun2])
        (hf2.of_cpu (close_cpu_step s2)) wp_a hp_eq hNext)
    rw [hline_eq, pointsToBytes_append]
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hc1)))))))
    sep_entail

/-- Full continuation-passing `SepWP` specification for `hashbrown_cli::parse_command`
    (`C.parseCommandAddr`), writing `ParseCmdSlot (parseCommand line) r0' r1' r2'` to the 24-byte
    output slot `[outPtr .. outPtr + 24)` using `128` bytes of stack (`80` B frame + `48` B for
    `strip_prefix`). -/
theorem hbParseCommand_wp {Q : Program} {C : HbCliLayout}
    {target ret_pc sp0 linePtr outPtr c0 c1 c2 : BitVec 64} {line : List (BitVec 8)}
    {s0 : State} {F : SepProp} {post : State → SepProp → Prop}
    (hc : HbMainCmdCode Q C)
    (hptr_nz : linePtr ≠ 0#64) (hptr_fit : linePtr.toNat + line.length < 2 ^ 64)
    (hpc : s0.pc = C.parseCommandAddr) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0) (hsp_al : s0.spAligned = true)
    (hlr : s0.readReg64 Reg.lr = ret_pc)
    (hx0 : s0.readReg64 .x0 = linePtr) (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 line.length)
    (hx8 : s0.readReg64 .x8 = outPtr)
    (hNext : ∀ (sf : State) (r0' r1' r2' : BitVec 64),
      ParseCmdSlot (parseCommand line) r0' r1' r2' →
      sf.pc = ret_pc → sf.status = .Running → PureCpuStep s0 sf →
      SepWP Q target sf
        ((linePtr ↦ₛ line) ∗ (outPtr ↦₆₄ r0') ∗ ((outPtr + 8#64) ↦₆₄ r1') ∗
         ((outPtr + 16#64) ↦₆₄ r2') ∗ HbParseRoData C ∗ stackAt sp0 128 ∗ F) post) :
    SepWP Q target s0
      ((linePtr ↦ₛ line) ∗ (outPtr ↦₆₄ c0) ∗ ((outPtr + 8#64) ↦₆₄ c1) ∗
       ((outPtr + 16#64) ↦₆₄ c2) ∗ HbParseRoData C ∗ stackAt sp0 128 ∗ F) post := by
  subst hsp
  have hcP := hc.parseCommand; have hcS := hc.stripPrefix; have hcB := hc.bytesEq
  have hcSp := hc.splitOnceSpace; have hcD := hc.parseDecimalU64
  have hsp_sub_al : ((s0.sp - 80#64) &&& 15#64 == 0#64) = true :=
    s0.spAligned_sub 80#64 hsp_al
  unpack_cmd_code hbParseCommandChunks hcP
  conv => arg 4; rw [parseCmd_stack_unpack s0.sp]
  unpack_cells 6
  wp_steps 6; wp_steps 1; wp_steps 4; wp_steps 1; norm_jmp
  dsimp only [HbParseRoData]
  refine SepWP.weaken_pre
      (by unfold parseCmdSavedRegs; sep_entail)
    (hbStripPrefix_wp hcS hcB (sp0 := s0.sp - 80#64) (pfx := pfxInsertBytes)
      (ret_pc := C.parseCommandAddr + 0x30#64)
      (F := (outPtr ↦₆₄ c0) ∗ ((outPtr + 8#64) ↦₆₄ c1) ∗ ((outPtr + 16#64) ↦₆₄ c2) ∗
            (C.pfxRemoveAddr ↦ᵣ pfxRemoveBytes) ∗ (C.pfxGetAddr ↦ᵣ pfxGetBytes) ∗
            (C.pfxContainsAddr ↦ᵣ pfxContainsBytes) ∗ (C.pfxWithCapAddr ↦ᵣ pfxWithCapBytes) ∗
            (C.cmdLenAddr ↦ᵣ cmdLenBytes) ∗ (C.cmdIsEmptyAddr ↦ᵣ cmdIsEmptyBytes) ∗
            (C.cmdClearAddr ↦ᵣ cmdClearBytes) ∗
            parseCmdSavedRegs s0.sp s0 ∗ memRegion (s0.sp - 80#64) 32 ∗ F)
      hptr_nz hptr_fit (by decide) wp_a (by simp [wp_norm, arm64_norm, hrun])
      wp_a (by simp only [State.spAligned, wp_norm, arm64_norm]
               simpa [BitVec.sub_eq_add_neg] using hsp_sub_al)
      wp_a wp_a wp_a wp_a rfl
      (fun s1 rest h1 hpc1 hrun1 hcpu1 hx0_1 hr_nz hx1_1 => ?_)
      (fun s1 h1 hpc1 hrun1 hcpu1 hx0_1 => ?_))
  · have hf1 : ParseCmdFrame s0 s1 := by
      rcases hcpu1 with ⟨hsp1, hfs1, htr1, haux1, hcs1⟩
      have hsp1_eq : s1.sp = s0.sp - 80#64 := hsp1.trans wp_a
      exact ⟨hsp1_eq, by simp only [State.spAligned, hsp1_eq]; exact hsp_sub_al,
        hfs1.trans (by simp [wp_norm, arm64_norm]),
        htr1.trans (by simp [wp_norm, arm64_norm]),
        (by simp [CpuAuxPreserved.refl s0] : CpuAuxPreserved s0 _).trans haux1,
        hcs1.vregs.trans (by simp [calleeSavedVRegs, wp_norm, arm64_norm]),
        hcs1.readReg64_x23.trans wp_a, hcs1.readReg64_x24.trans wp_a,
        hcs1.readReg64_x25.trans wp_a, hcs1.readReg64_x26.trans wp_a,
        hcs1.readReg64_x27.trans wp_a, hcs1.readReg64_x28.trans wp_a⟩
    have hx19_1 : s1.readReg64 .x19 = outPtr := hcpu1.2.2.2.2.readReg64_x19.trans wp_a
    refine SepWP.weaken_pre (by unfold HbParseRoData; sep_entail)
      (parseCmd_insertRest_wp hcP hcSp hcD hlr hptr_fit h1 hr_nz hpc1 hrun1
        hf1 hx19_1 hx0_1 hx1_1 hNext)
  · have hf1 : ParseCmdFrame s0 s1 := by
      rcases hcpu1 with ⟨hsp1, hfs1, htr1, haux1, hcs1⟩
      have hsp1_eq : s1.sp = s0.sp - 80#64 := hsp1.trans wp_a
      exact ⟨hsp1_eq, by simp only [State.spAligned, hsp1_eq]; exact hsp_sub_al,
        hfs1.trans (by simp [wp_norm, arm64_norm]),
        htr1.trans (by simp [wp_norm, arm64_norm]),
        (by simp [CpuAuxPreserved.refl s0] : CpuAuxPreserved s0 _).trans haux1,
        hcs1.vregs.trans (by simp [calleeSavedVRegs, wp_norm, arm64_norm]),
        hcs1.readReg64_x23.trans wp_a, hcs1.readReg64_x24.trans wp_a,
        hcs1.readReg64_x25.trans wp_a, hcs1.readReg64_x26.trans wp_a,
        hcs1.readReg64_x27.trans wp_a, hcs1.readReg64_x28.trans wp_a⟩
    have hx19_1 : s1.readReg64 .x19 = outPtr := hcpu1.2.2.2.2.readReg64_x19.trans wp_a
    have hx20_1 : s1.readReg64 .x20 = BitVec.ofNat 64 line.length :=
      hcpu1.2.2.2.2.readReg64_x20.trans wp_a
    have hx21_1 : s1.readReg64 .x21 = linePtr := hcpu1.2.2.2.2.readReg64_x21.trans wp_a
    have hx0_1' : s1.readReg64 (.gpr 0#5) = 0#64 := hx0_1
    wp_steps 1
    refine SepWP.weaken_pre (by unfold HbParseRoData; sep_entail)
      (parseCmd_from0x74_wp hcP hcS hcB hcD hlr hptr_nz hptr_fit h1
        wp_a (by simp [wp_norm, arm64_norm, hrun1])
        (hf1.of_cpu (close_cpu_step s1)) wp_a wp_a wp_a hNext)

end CaseStudies.Hashbrown.Proofs.StdCli
