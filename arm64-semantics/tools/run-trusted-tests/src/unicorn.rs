// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Unicorn Engine (`UC_ARCH_ARM64` / QEMU AArch64) single-test execution harness (`[TEST ONLY]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[TEST ONLY]` (reference AArch64 CPU emulator oracle for differential testing
//!   of Lean 4 ISA semantics in `Arm64/`).
//! - **Purpose:** Thin adapter over [`unicorn_aarch64::UnicornOracle`]: converts a
//!   [`DiffTestCase`] into an [`isa_oracle::TestInput`] via [`DiffTestCase::to_test_input`],
//!   runs it through [`unicorn_aarch64::UnicornOracle`], and returns its [`OracleState`].
//!
//! # Key Types & Functions
//! - [`UC_X_REGS`] and [`UC_V_REGS`]: Re-exported register tables from [`unicorn_aarch64`].
//! - [`run_unicorn`]: Executes one [`DiffTestCase`] in [`unicorn_aarch64::UnicornOracle`] and
//!   returns its [`OracleState`].
//!
//! # When to Read This File
//! - Read this file to see how `run-trusted-tests` invokes the [`unicorn_aarch64`] crate.
//! - For the Unicorn [`Arm64Oracle`] implementation, read `tools/unicorn-aarch64/src/lib.rs`
//!   and `tools/unicorn-aarch64/README.md`.

use anyhow::{Result, anyhow};
use isa_oracle::{Arm64Oracle, Outcome};
pub use unicorn_aarch64::{UC_V_REGS, UC_X_REGS, UnicornOracle};

use crate::model::{DiffTestCase, OracleState};

/// Execute `tc` in Unicorn Engine (`UC_ARCH_ARM64`) and return its final architectural state.
pub fn run_unicorn(tc: &DiffTestCase) -> Result<OracleState> {
    let input = tc.to_test_input()?;
    let mut oracle = UnicornOracle::new().map_err(|e| anyhow!("{e}"))?;
    let outcome = oracle.run(&input);
    match &outcome {
        Outcome::Ok { .. } => Ok(OracleState::from_outcome(&outcome)),
        other => Err(anyhow!(
            "Unicorn emu_start failed on `{}`: {}",
            tc.name,
            other.summary()
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::{DEFAULT_CODE_BASE, DEFAULT_DATA_BASE, DEFAULT_EXIT_PC};
    use serde_json::json;

    #[test]
    fn test_unicorn_executes_add_and_ret() {
        let mut regs: Vec<serde_json::Value> =
            (0..31).map(|_| json!("0x0000000000000000")).collect();
        regs[0] = json!("0x0000000000000014"); // 20
        regs[1] = json!("0x0000000000000016"); // 22
        regs[30] = json!(format!("0x{DEFAULT_EXIT_PC:016x}"));
        let tc = DiffTestCase {
            name: "unit_add".to_string(),
            asm: None,
            base_pc: format!("0x{DEFAULT_CODE_BASE:016x}"),
            start_pc: None,
            exit_pc: format!("0x{DEFAULT_EXIT_PC:016x}"),
            max_steps: 10,
            words: vec![
                "0x8b010000".to_string(), // add x0, x0, x1
                "0xd65f03c0".to_string(), // ret
            ],
            regs,
            vregs: vec![],
            sp: format!("0x{:016x}", DEFAULT_DATA_BASE + 0x8000),
            nzcv: 0,
            mem_init: vec![],
            mem_watch: vec![],
            skip_sail: None,
        };

        let st = run_unicorn(&tc).expect("Unicorn execution succeeds");
        assert_eq!(st.regs[0], "0x000000000000002a");
        assert_eq!(st.pc, format!("0x{DEFAULT_EXIT_PC:016x}"));
    }
}
