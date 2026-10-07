#!/usr/bin/env python3
"""Capture both kernels' assumptions for nested compilation and copying."""

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from experiments.issue624.register_assumptions import entries
from scripts.check_proof_status import query_assumptions


REGISTER = {
    "loop_reaches", "loopRun_repeat", "loopCost_repeat",
    "registerAt_putRegister_other", "loopRun_regs_length", "loopRun_readOnly",
    "programRun_regs_length", "programRun_readOnly", "clear_state_reaches",
    "literal_state_reaches", "compileProgram_reaches", "addToProgram_wellFormed",
    "incrementRegs_registerAt", "loopRun_counter_zero", "loopRun_adds", "loopRun_out",
    "addToProgram_registers", "addToProgram_out", "addToProgram_reaches",
    "register_span", "putRegister_size_le", "loopCost_straight_bound",
    "loopRun_straight_size_le", "addToProgram_cost_polynomial",
}


def reports():
    result = {}
    for language in ("lean", "rocq"):
        result[language] = [entry for entry in entries(language)
                            if entry["theorem"].rsplit(".", 1)[1] in REGISTER]
        found = {entry["theorem"].rsplit(".", 1)[1] for entry in result[language]}
        if found != REGISTER:
            raise ValueError(f"{language}: missing conclusions: {sorted(REGISTER - found)}")
        for entry in result[language]:
            entry["allowed_axioms"] = sorted(query_assumptions(ROOT, language, entry))
    return result


if __name__ == "__main__":
    print(json.dumps(reports(), indent=2))
