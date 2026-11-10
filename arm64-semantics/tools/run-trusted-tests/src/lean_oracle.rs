// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Persistent out-of-process `LeanOracle` adapter over `diff_eval --serve` (`[TEST ONLY]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[TEST ONLY]` (wraps the Lean 4 `Arm64` operational semantics executable
//!   `diff_eval --serve` behind [`isa_oracle::Arm64Oracle`]).
//! - **Purpose:** Spawns `diff_eval --serve` once as a persistent child process and communicates
//!   over stdin/stdout using the framed little-endian binary protocol implemented by
//!   `Arm64/Testing/Harness/Serve.lean`:
//!   - `CMD_LOAD` (`0x01`): Load a [`TestInput`] into the server's `ServedSession`.
//!   - `CMD_STEP` (`0x02`): Step 1 instruction and return the post-step [`Outcome`].
//!   - `CMD_RUN` (`0x03`): Load a [`TestInput`], step up to `max_steps` until `exit_pc`, and return
//!     the final [`Outcome`].
//!   - `CMD_READ` (`0x04`): Read the current [`CpuState`] and watched memory slices.
//!   - `CMD_RUN_BATCH` (`0x05`): Evaluate a slice of [`TestInput`]s in parallel across 32 Lean
//!     `Task.spawn` workers and return one [`Outcome`] per input.
//!
//! # Key Types & Functions
//! - [`LeanOracle`]: Persistent child-process handle implementing [`Arm64Oracle`].
//! - [`encode_test_input`], [`decode_outcome`]: Binary wire serialization matching
//!   `Arm64/Testing/Harness/Serve.lean`.
//!
//! # When to Read This File
//! - Read this file when modifying the `LeanOracle` IPC client or the binary wire format shared
//!   with `Arm64/Testing/Harness/Serve.lean`.

use std::io::{BufReader, BufWriter, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};

use isa_oracle::{Arm64Oracle, CpuState, FaultKind, Outcome, TestInput};

const CMD_QUIT: u8 = 0x00;
const CMD_LOAD: u8 = 0x01;
const CMD_STEP: u8 = 0x02;
const CMD_RUN: u8 = 0x03;
const CMD_READ: u8 = 0x04;
const CMD_RUN_BATCH: u8 = 0x05;

/// Serialize a [`CpuState`] (`801` bytes, little-endian) into `buf`.
pub fn encode_cpu_state(buf: &mut Vec<u8>, state: &CpuState) {
    for &r in &state.gprs {
        buf.extend_from_slice(&r.to_le_bytes());
    }
    for &v in &state.vregs {
        let lo = v as u64;
        let hi = (v >> 64) as u64;
        buf.extend_from_slice(&lo.to_le_bytes());
        buf.extend_from_slice(&hi.to_le_bytes());
    }
    buf.extend_from_slice(&state.sp.to_le_bytes());
    buf.extend_from_slice(&state.pc.to_le_bytes());
    buf.push(state.nzcv & 0xF);
    buf.extend_from_slice(&state.fpcr.to_le_bytes());
    buf.extend_from_slice(&state.fpsr.to_le_bytes());
    buf.extend_from_slice(&state.tpidr_el0.to_le_bytes());
}

/// Serialize a [`TestInput`] into `buf` matching `Testing.Harness.decodeTestInput` in `Serve.lean`.
pub fn encode_test_input(buf: &mut Vec<u8>, input: &TestInput) {
    encode_cpu_state(buf, &input.state);
    buf.extend_from_slice(&input.exit_pc.to_le_bytes());
    buf.extend_from_slice(&(input.max_steps as u64).to_le_bytes());

    buf.extend_from_slice(&(input.code.len() as u32).to_le_bytes());
    for (base_pc, words) in &input.code {
        buf.extend_from_slice(&base_pc.to_le_bytes());
        buf.extend_from_slice(&(words.len() as u32).to_le_bytes());
        for &w in words {
            buf.extend_from_slice(&w.to_le_bytes());
        }
    }

    buf.extend_from_slice(&(input.mem.len() as u32).to_le_bytes());
    for (addr, bytes) in &input.mem {
        buf.extend_from_slice(&addr.to_le_bytes());
        buf.extend_from_slice(&(bytes.len() as u32).to_le_bytes());
        buf.extend_from_slice(bytes);
    }

    buf.extend_from_slice(&(input.mapped.len() as u32).to_le_bytes());
    for r in &input.mapped {
        buf.extend_from_slice(&r.start.to_le_bytes());
        buf.extend_from_slice(&r.end.to_le_bytes());
    }

    buf.extend_from_slice(&(input.watch.len() as u32).to_le_bytes());
    for r in &input.watch {
        buf.extend_from_slice(&r.start.to_le_bytes());
        buf.extend_from_slice(&r.end.to_le_bytes());
    }
}

fn read_u8(bytes: &[u8], off: &mut usize) -> Result<u8, String> {
    if *off + 1 > bytes.len() {
        return Err("unexpected EOF reading u8 from diff_eval --serve".to_string());
    }
    let v = bytes[*off];
    *off += 1;
    Ok(v)
}

fn read_u32(bytes: &[u8], off: &mut usize) -> Result<u32, String> {
    if *off + 4 > bytes.len() {
        return Err("unexpected EOF reading u32 from diff_eval --serve".to_string());
    }
    let mut b = [0u8; 4];
    b.copy_from_slice(&bytes[*off..*off + 4]);
    *off += 4;
    Ok(u32::from_le_bytes(b))
}

fn read_u64(bytes: &[u8], off: &mut usize) -> Result<u64, String> {
    if *off + 8 > bytes.len() {
        return Err("unexpected EOF reading u64 from diff_eval --serve".to_string());
    }
    let mut b = [0u8; 8];
    b.copy_from_slice(&bytes[*off..*off + 8]);
    *off += 8;
    Ok(u64::from_le_bytes(b))
}

/// Deserialize a [`CpuState`] (`801` bytes, little-endian) from `bytes[*off..]`.
pub fn decode_cpu_state(bytes: &[u8], off: &mut usize) -> Result<CpuState, String> {
    if *off + 801 > bytes.len() {
        return Err(format!(
            "truncated CpuState in diff_eval --serve response ({} bytes remaining)",
            bytes.len().saturating_sub(*off)
        ));
    }
    let mut gprs = [0u64; 31];
    for r in &mut gprs {
        *r = read_u64(bytes, off)?;
    }
    let mut vregs = [0u128; 32];
    for v in &mut vregs {
        let lo = read_u64(bytes, off)? as u128;
        let hi = read_u64(bytes, off)? as u128;
        *v = (hi << 64) | lo;
    }
    let sp = read_u64(bytes, off)?;
    let pc = read_u64(bytes, off)?;
    let nzcv = read_u8(bytes, off)? & 0xF;
    let fpcr = read_u64(bytes, off)?;
    let fpsr = read_u64(bytes, off)?;
    let tpidr_el0 = read_u64(bytes, off)?;
    Ok(CpuState {
        gprs,
        vregs,
        sp,
        pc,
        nzcv,
        fpcr,
        fpsr,
        tpidr_el0,
    })
}

/// Deserialize one [`Outcome`] from `bytes[*off..]` matching `Testing.Harness.pushOutcome` in `Serve.lean`.
pub fn decode_outcome(bytes: &[u8], off: &mut usize) -> Result<Outcome, String> {
    let tag = read_u8(bytes, off)?;
    match tag {
        0 => {
            let state = decode_cpu_state(bytes, off)?;
            let steps = read_u64(bytes, off)? as usize;
            let num_mem = read_u32(bytes, off)? as usize;
            let mut mem = Vec::with_capacity(num_mem);
            for _ in 0..num_mem {
                let addr = read_u64(bytes, off)?;
                let len = read_u32(bytes, off)? as usize;
                if *off + len > bytes.len() {
                    return Err("truncated watched memory slice in Outcome::Ok".to_string());
                }
                let slice = bytes[*off..*off + len].to_vec();
                *off += len;
                mem.push((addr, slice));
            }
            Ok(Outcome::Ok { state, mem, steps })
        }
        1 => {
            let pc = read_u64(bytes, off)?;
            let word = read_u32(bytes, off)?;
            Ok(Outcome::Unmodeled { pc, word })
        }
        2 => {
            let pc = read_u64(bytes, off)?;
            let kind_byte = read_u8(bytes, off)?;
            let kind = match kind_byte {
                0 => FaultKind::Unmapped,
                1 => FaultKind::Misaligned,
                2 => FaultKind::Undefined,
                3 => FaultKind::Svc,
                _ => FaultKind::Other,
            };
            Ok(Outcome::Fault { pc, kind })
        }
        3 => {
            let pc = read_u64(bytes, off)?;
            Ok(Outcome::StepLimit { pc })
        }
        4 => {
            let len = read_u32(bytes, off)? as usize;
            if *off + len > bytes.len() {
                return Err("truncated error message in Outcome::OracleError".to_string());
            }
            let msg = String::from_utf8_lossy(&bytes[*off..*off + len]).into_owned();
            *off += len;
            Ok(Outcome::OracleError(msg))
        }
        other => Err(format!(
            "unknown Outcome tag {other} from diff_eval --serve"
        )),
    }
}

/// Persistent out-of-process [`Arm64Oracle`] backed by `diff_eval --serve`.
pub struct LeanOracle {
    diff_eval_bin: PathBuf,
    child: Child,
    stdin: BufWriter<ChildStdin>,
    stdout: BufReader<ChildStdout>,
    tx_buf: Vec<u8>,
}

impl LeanOracle {
    /// Spawn `diff_eval --serve` and return a connected [`LeanOracle`].
    pub fn new(diff_eval_bin: impl AsRef<Path>) -> Result<Self, String> {
        let bin = diff_eval_bin.as_ref().to_path_buf();
        let mut cmd = Command::new(&bin);
        cmd.arg("--serve");
        Self::spawn_with_command(&mut cmd, bin)
    }

    pub(crate) fn spawn_with_command(
        cmd: &mut Command,
        diff_eval_bin: PathBuf,
    ) -> Result<Self, String> {
        let mut child = cmd
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()
            .map_err(|e| format!("failed to spawn `{}` --serve: {e}", diff_eval_bin.display()))?;
        let stdin = BufWriter::with_capacity(
            64 * 1024,
            child
                .stdin
                .take()
                .ok_or_else(|| "failed to capture stdin of diff_eval --serve".to_string())?,
        );
        let stdout = BufReader::with_capacity(
            64 * 1024,
            child
                .stdout
                .take()
                .ok_or_else(|| "failed to capture stdout of diff_eval --serve".to_string())?,
        );
        Ok(Self {
            diff_eval_bin,
            child,
            stdin,
            stdout,
            tx_buf: Vec::with_capacity(4096),
        })
    }

    /// Path to the `diff_eval` binary backing this oracle.
    pub fn diff_eval_bin(&self) -> &Path {
        &self.diff_eval_bin
    }

    fn send_frame(&mut self, payload: &[u8]) -> Result<(), String> {
        let len = payload.len() as u32;
        self.stdin
            .write_all(&len.to_le_bytes())
            .map_err(|e| format!("failed to write frame header to diff_eval --serve: {e}"))?;
        self.stdin
            .write_all(payload)
            .map_err(|e| format!("failed to write frame payload to diff_eval --serve: {e}"))?;
        self.stdin
            .flush()
            .map_err(|e| format!("failed to flush stdin to diff_eval --serve: {e}"))
    }

    fn recv_frame(&mut self) -> Result<Vec<u8>, String> {
        let mut hdr = [0u8; 4];
        self.stdout
            .read_exact(&mut hdr)
            .map_err(|e| format!("failed to read frame header from diff_eval --serve: {e}"))?;
        let len = u32::from_le_bytes(hdr) as usize;
        let mut buf = vec![0u8; len];
        self.stdout
            .read_exact(&mut buf)
            .map_err(|e| format!("failed to read {len}-byte frame from diff_eval --serve: {e}"))?;
        Ok(buf)
    }

    /// Query the currently loaded [`CpuState`] and watched memory via `CMD_READ`.
    pub fn read_current(&mut self) -> Outcome {
        if let Err(e) = self.send_frame(&[CMD_READ]) {
            return Outcome::OracleError(e);
        }
        match self.recv_frame() {
            Ok(resp) => {
                let mut off = 0;
                decode_outcome(&resp, &mut off).unwrap_or_else(Outcome::OracleError)
            }
            Err(e) => Outcome::OracleError(e),
        }
    }
}

impl Arm64Oracle for LeanOracle {
    fn name(&self) -> &'static str {
        "Lean"
    }

    fn load(&mut self, input: &TestInput) -> Result<(), String> {
        self.tx_buf.clear();
        self.tx_buf.push(CMD_LOAD);
        encode_test_input(&mut self.tx_buf, input);
        let payload = std::mem::take(&mut self.tx_buf);
        let res = self.send_frame(&payload);
        self.tx_buf = payload;
        res?;
        let ack = self.recv_frame()?;
        if ack.first().copied() == Some(0) {
            Ok(())
        } else {
            Err("diff_eval --serve rejected CMD_LOAD payload".to_string())
        }
    }

    fn step(&mut self) -> Outcome {
        if let Err(e) = self.send_frame(&[CMD_STEP]) {
            return Outcome::OracleError(e);
        }
        match self.recv_frame() {
            Ok(resp) => {
                let mut off = 0;
                decode_outcome(&resp, &mut off).unwrap_or_else(Outcome::OracleError)
            }
            Err(e) => Outcome::OracleError(e),
        }
    }

    fn run(&mut self, input: &TestInput) -> Outcome {
        self.tx_buf.clear();
        self.tx_buf.push(CMD_RUN);
        encode_test_input(&mut self.tx_buf, input);
        let payload = std::mem::take(&mut self.tx_buf);
        let send_res = self.send_frame(&payload);
        self.tx_buf = payload;
        if let Err(e) = send_res {
            return Outcome::OracleError(e);
        }
        match self.recv_frame() {
            Ok(resp) => {
                let mut off = 0;
                decode_outcome(&resp, &mut off).unwrap_or_else(Outcome::OracleError)
            }
            Err(e) => Outcome::OracleError(e),
        }
    }

    fn run_batch(&mut self, inputs: &[TestInput]) -> Vec<Outcome> {
        if inputs.is_empty() {
            return Vec::new();
        }
        self.tx_buf.clear();
        self.tx_buf.reserve(5 + inputs.len() * 880);
        self.tx_buf.push(CMD_RUN_BATCH);
        self.tx_buf
            .extend_from_slice(&(inputs.len() as u32).to_le_bytes());
        for inp in inputs {
            encode_test_input(&mut self.tx_buf, inp);
        }
        let payload = std::mem::take(&mut self.tx_buf);
        let send_res = self.send_frame(&payload);
        self.tx_buf = payload;
        if let Err(e) = send_res {
            return vec![Outcome::OracleError(e); inputs.len()];
        }
        let resp = match self.recv_frame() {
            Ok(r) => r,
            Err(e) => return vec![Outcome::OracleError(e); inputs.len()],
        };
        let mut off = 0;
        let count = match read_u32(&resp, &mut off) {
            Ok(c) => c as usize,
            Err(e) => return vec![Outcome::OracleError(e); inputs.len()],
        };
        if count != inputs.len() {
            return vec![
                Outcome::OracleError(format!(
                    "diff_eval --serve RUN_BATCH returned {count} outcomes for {} inputs",
                    inputs.len()
                ));
                inputs.len()
            ];
        }
        let mut outcomes = Vec::with_capacity(count);
        for _ in 0..count {
            match decode_outcome(&resp, &mut off) {
                Ok(o) => outcomes.push(o),
                Err(e) => {
                    outcomes.push(Outcome::OracleError(e));
                }
            }
        }
        outcomes
    }
}

impl Drop for LeanOracle {
    fn drop(&mut self) {
        let _ = self.send_frame(&[CMD_QUIT]);
        let _ = self.child.wait();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const CODE_BASE: u64 = 0x0001_0000;
    const STACK_BASE: u64 = 0x0002_8000;

    #[test]
    fn test_lean_oracle_nop_identity_roundtrip() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .parent()
            .unwrap();
        let diff_eval_bin =
            crate::ensure_diff_eval_bin(root, None).expect("ensure_diff_eval_bin succeeds");

        let mut init = CpuState::new(CODE_BASE, STACK_BASE);
        for i in 0..31 {
            init.set_x(i, 0x0101_0101_0101_0101u64.wrapping_mul((i as u64) + 1));
        }
        for i in 0..32 {
            let lo = 0xaaaa_0000_0000_0000u64 | (i as u64);
            let hi = 0xbbbb_0000_0000_0000u64 | ((i as u64) << 8);
            init.set_v(i, ((hi as u128) << 64) | (lo as u128));
        }
        init.nzcv = 0b1010;
        init.fpcr = 0;
        init.fpsr = 0x10;
        init.tpidr_el0 = 0x0000_7fff_dead_beef;

        let mut input = TestInput::single_insn(init.clone(), isa_oracle::AARCH64_NOP_WORD);
        input.mem = vec![(
            0x0002_0000,
            vec![0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88],
        )];
        input.mapped.push(0x0002_0000..0x0002_1000);
        input.watch = vec![0x0002_0000..0x0002_0008];

        let mut oracle = LeanOracle::new(&diff_eval_bin).expect("LeanOracle::new succeeds");
        let out = oracle.run(&input);
        let mut expected = init;
        expected.pc = CODE_BASE + 4;
        assert_eq!(
            out,
            Outcome::Ok {
                state: expected,
                mem: vec![(
                    0x0002_0000,
                    vec![0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88]
                )],
                steps: 1,
            }
        );

        // Also test load + step + run_batch reuse on the same persistent LeanOracle process.
        oracle.load(&input).expect("LeanOracle::load succeeds");
        let step_out = oracle.step();
        assert_eq!(step_out, out);

        let batch_out = oracle.run_batch(&[input.clone(), input]);
        assert_eq!(batch_out, vec![out.clone(), out]);

        // Non-zero FPCR must be rejected (fail-closed) by the persistent Lean oracle server.
        let mut bad_fpcr_init = CpuState::new(CODE_BASE, STACK_BASE);
        bad_fpcr_init.fpcr = 1 << 22;
        let bad_fpcr_input = TestInput::single_insn(bad_fpcr_init, isa_oracle::AARCH64_NOP_WORD);
        assert_eq!(
            oracle.run(&bad_fpcr_input),
            Outcome::Fault {
                pc: CODE_BASE,
                kind: FaultKind::Other,
            }
        );

        // Probe MSR FPSR, ~0; MRS X1, FPSR across LeanOracle and SailOracle.
        let mut probe_init = CpuState::new(CODE_BASE, STACK_BASE);
        probe_init.set_x(0, u64::MAX);
        let probe_input = TestInput {
            state: probe_init,
            code: vec![(CODE_BASE, vec![0xd51b_4420, 0xd53b_4421])],
            mem: Vec::new(),
            mapped: vec![CODE_BASE..(CODE_BASE + 0x1000)],
            watch: Vec::new(),
            exit_pc: CODE_BASE + 8,
            max_steps: 4,
        };
        let lean_probe = oracle.run(&probe_input);
        let mut sail = sail_aarch64::SailOracle::new().expect("SailOracle::new succeeds");
        let sail_probe = sail.run(&probe_input);
        match (lean_probe, sail_probe) {
            (Outcome::Ok { state: ls, .. }, Outcome::Ok { state: ss, .. }) => {
                assert_eq!(ls.fpsr, isa_oracle::FPSR_MASK);
                assert_eq!(ls.x(1), isa_oracle::FPSR_MASK);
                assert_eq!(ss.fpsr & isa_oracle::FPSR_MASK, isa_oracle::FPSR_MASK);
                assert_eq!(ss.x(1) & isa_oracle::FPSR_MASK, isa_oracle::FPSR_MASK);
            }
            other => panic!("expected Ok outcomes from Lean and Sail FPSR probe, got {other:?}"),
        }
    }
}
