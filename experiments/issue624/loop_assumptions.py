#!/usr/bin/env python3
"""Capture both kernels' assumptions for the charged unary loop and emitter."""

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from experiments.issue624.register_assumptions import entries
from scripts.check_proof_status import query_assumptions


REGISTER = {
    "repeatHead_states", "repeatBase_states", "repeatMachine_states",
    "repeatHeadTarget_inside", "repeatTarget_inside", "repeatHeadTarget_positive",
    "repeatHeadTarget_empty", "repeatTarget_back", "repeatTarget_exit", "repeat_empty",
    "repeat_positive", "similar_shiftConfig", "similar_retargetConfig", "repeat_body_reaches",
    "registerAt_split", "putRegister_split", "putRegister_length", "registerAt_putRegister",
    "incrementRegs_readOnly", "runProg_readOnly", "repeatPrefix_split", "repeatSuffix_split",
    "repeat_compile_reaches", "repeatRun_ticks", "repeatCost_ticks", "ticksTime_polynomial",
    "emitTicks_reaches", "compose_home_reaches", "ticks_eq_replicate", "literalTime_polynomial",
    "emitLiteral_reaches",
}


def reports():
    result = {}
    for language in ("lean", "rocq"):
        result[language] = [entry for entry in entries(language)
                            if entry["theorem"].rsplit(".", 1)[1] in REGISTER]
        for entry in result[language]:
            entry["allowed_axioms"] = sorted(query_assumptions(ROOT, language, entry))
    return result


if __name__ == "__main__":
    print(json.dumps(reports(), indent=2))
