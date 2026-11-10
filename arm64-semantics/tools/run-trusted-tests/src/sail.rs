// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Official Sail Armv9.4-A (`rems-project/sail-arm`) single-test execution harness (`[TEST ONLY]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[TEST ONLY]` (authoritative ASL-derived Sail Armv9.4-A ISA oracle for
//!   differential testing of Lean 4 ISA semantics in `Arm64/`).
//! - **Purpose:** Thin adapter over [`sail_aarch64::SailOracle`]: converts a [`DiffTestCase`]
//!   into an [`isa_oracle::TestInput`] via [`DiffTestCase::to_test_input`], runs it through
//!   [`sail_aarch64::SailOracle`], and returns its [`OracleState`].
//!
//! # Key Types & Functions
//! - [`run_sail`]: Executes one [`DiffTestCase`] in [`sail_aarch64::SailOracle`] and returns its
//!   [`OracleState`].
//!
//! # When to Read This File
//! - Read this file to see how `run-trusted-tests` invokes the [`sail_aarch64`] crate.
//! - For the Sail C model FFI and [`Arm64Oracle`] implementation, read
//!   `tools/sail-aarch64/src/lib.rs` and `tools/sail-aarch64/README.md`.

use anyhow::{Result, anyhow};
use isa_oracle::{Arm64Oracle, Outcome};
use sail_aarch64::SailOracle;

use crate::model::{DiffTestCase, OracleState};

/// Execute `tc` in the authoritative Sail Armv9.4-A simulator and return its final architectural state.
pub fn run_sail(tc: &DiffTestCase) -> Result<OracleState> {
    let input = tc.to_test_input()?;
    let mut oracle = SailOracle::new()?;
    let outcome = oracle.run(&input);
    match &outcome {
        Outcome::Ok { .. } => Ok(OracleState::from_outcome(&outcome)),
        other => Err(anyhow!(
            "Sail step_model faulted on `{}`: {}",
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
    fn test_sail_executes_add_and_ret() {
        let mut regs: Vec<serde_json::Value> =
            (0..31).map(|_| json!("0x0000000000000000")).collect();
        regs[0] = json!("0x0000000000000014"); // 20
        regs[1] = json!("0x0000000000000016"); // 22
        regs[30] = json!(format!("0x{DEFAULT_EXIT_PC:016x}"));
        let tc = DiffTestCase {
            name: "unit_sail_add".to_string(),
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

        let st = run_sail(&tc).expect("Sail execution succeeds");
        assert_eq!(st.regs[0], "0x000000000000002a");
        assert_eq!(st.pc, format!("0x{DEFAULT_EXIT_PC:016x}"));
    }
}
