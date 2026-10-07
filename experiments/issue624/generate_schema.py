"""Generate both tableau schema descriptions from the same expression trees.

The generated regions contain finite syntax data, never prover functions or
machine-cost oracles. Proofs after the marker are maintained in each prover.
Run with --check in CI to catch drift.
"""

from pathlib import Path
import argparse

ROOT = Path(__file__).resolve().parents[2]
MARKERS = {
    "lean": "-- END GENERATED SCHEMA DATA\n",
    "rocq": "(* END GENERATED SCHEMA DATA *)\n",
}

# Core semantics are small and use the existing Lit/CNF types. Indices are
# named loop slots so a nested loop cannot silently shift a captured index.
LEAN_CORE = """import proofs.experiments.issue624.lean.InitialCNF

/-! Generated schema syntax and data. Regenerate with
`python3 experiments/issue624/generate_schema.py`. The arithmetic product is
needed for row index * variable stride; literal ranges encode long clauses.
No second CNF evaluator or trace semantics is introduced. -/
namespace Issue624.Schema
open Complexity Issue532.Machines Issue624.LocalCNF Issue624.MachineCNF
open Issue624.SuccessorCNF Issue624.RunCNF Issue624.InitialCNF
open Issue624.CertificateCNF Issue624.VerifierTableau Issue624.FixedWindow

inductive Expr where
  | const (value : Nat) | param (slot : Nat) | idx (slot : Nat)
  | bit (position : Expr)
  | add (a b : Expr) | mul (a b : Expr) | sub (a b : Expr)
  | selectEq (a b yes no : Expr)
  deriving Repr, DecidableEq

def setIndex (indices : Nat → Nat) (slot value : Nat) : Nat → Nat :=
  fun k => if k = slot then value else indices k

def evalExpr (e : Expr) (params : List Nat) (x : Word) (indices : Nat → Nat) : Nat :=
  match e with
  | .const n => n | .param k => (params[k]?).getD 0 | .idx k => indices k
  | .bit e => if (x[evalExpr e params x indices]?).getD false then 1 else 0
  | .add a b => evalExpr a params x indices + evalExpr b params x indices
  | .mul a b => evalExpr a params x indices * evalExpr b params x indices
  | .sub a b => evalExpr a params x indices - evalExpr b params x indices
  | .selectEq a b yes no => if evalExpr a params x indices = evalExpr b params x indices
      then evalExpr yes params x indices else evalExpr no params x indices

inductive Literals where
  | list (values : List (Expr × Bool))
  | append (a b : Literals)
  | range (slot : Nat) (count value : Expr) (pos : Bool)
  deriving Repr, DecidableEq

def evalLiterals (ls : Literals) (params : List Nat) (x : Word) (indices : Nat → Nat) : Clause :=
  match ls with
  | .list vs => vs.map fun (e, p) => ⟨evalExpr e params x indices, p⟩
  | .append a b => evalLiterals a params x indices ++ evalLiterals b params x indices
  | .range slot count value pos => (List.range (evalExpr count params x indices)).map
      fun i => ⟨evalExpr value params x (setIndex indices slot i), pos⟩

inductive Schema where
  | empty | clause (values : Literals) | seq (a b : Schema)
  | forRange (slot : Nat) (count : Expr) (body : Schema)
  | ifLt (a b : Expr) (yes no : Schema)
  | guard (guards : Literals) (body : Schema)
  deriving Repr, DecidableEq

def evalSchema (s : Schema) (params : List Nat) (x : Word) (indices : Nat → Nat) : CNF :=
  match s with
  | .empty => [] | .clause vs => [evalLiterals vs params x indices]
  | .seq a b => evalSchema a params x indices ++ evalSchema b params x indices
  | .forRange slot count body => (List.range (evalExpr count params x indices)).flatMap
      fun i => evalSchema body params x (setIndex indices slot i)
  | .ifLt a b yes no => if evalExpr a params x indices < evalExpr b params x indices
      then evalSchema yes params x indices else evalSchema no params x indices
  | .guard guards body => (evalSchema body params x indices).map
      fun c => evalLiterals guards params x indices ++ c

def seqSchemas (ss : List Schema) : Schema := ss.foldr Schema.seq .empty

"""
ROCQ_CORE = """From Stdlib Require Import List Bool Arith Lia.
From proofs.complexity.rocq Require Import Complexity.
From proofs.experiments.issue532.rocq Require Import Machines.
From proofs.experiments.issue624.rocq Require Import
  LocalCNF MachineCNF SuccessorCNF RunCNF InitialCNF CertificateCNF VerifierTableau FixedWindow.
Import ListNotations.

(** Generated schema syntax and data: run generate_schema.py. Products support
    row strides; literal ranges support long clauses. Uses the existing CNF. *)
Module Schema.
Import Complexity Machines LocalCNF MachineCNF SuccessorCNF RunCNF InitialCNF.
Import CertificateCNF VerifierTableau FixedWindow.

Inductive Expr :=
| EConst (value : nat) | EParam (slot : nat) | EIdx (slot : nat)
| EBit (position : Expr)
| EAdd (a b : Expr) | EMul (a b : Expr) | ESub (a b : Expr)
| ESelectEq (a b yes no : Expr).
Definition setIndex (indices : nat -> nat) (slot value : nat) :=
  fun k => if Nat.eqb k slot then value else indices k.
Fixpoint evalExpr (e : Expr) (params : list nat) (x : Word) (indices : nat -> nat) : nat :=
  match e with
  | EConst n => n | EParam k => nth k params 0 | EIdx k => indices k
  | EBit e => if nth (evalExpr e params x indices) x false then 1 else 0
  | EAdd a b => evalExpr a params x indices + evalExpr b params x indices
  | EMul a b => evalExpr a params x indices * evalExpr b params x indices
  | ESub a b => evalExpr a params x indices - evalExpr b params x indices
  | ESelectEq a b yes no => if Nat.eqb (evalExpr a params x indices) (evalExpr b params x indices)
      then evalExpr yes params x indices else evalExpr no params x indices
  end.
Inductive Literals :=
| LList (values : list (Expr * bool)) | LAppend (a b : Literals)
| LRange (slot : nat) (count value : Expr) (pos : bool).
Fixpoint evalLiterals (ls : Literals) (params : list nat) (x : Word) (indices : nat -> nat) : Clause :=
  match ls with
  | LList vs => map (fun ep => mkLit (evalExpr (fst ep) params x indices) (snd ep)) vs
  | LAppend a b => evalLiterals a params x indices ++ evalLiterals b params x indices
  | LRange slot count value pos => map
      (fun i => mkLit (evalExpr value params x (setIndex indices slot i)) pos)
      (seq 0 (evalExpr count params x indices))
  end.
Inductive Schema :=
| SEmpty | SClause (values : Literals) | SSeq (a b : Schema)
| SForRange (slot : nat) (count : Expr) (body : Schema)
| SIfLt (a b : Expr) (yes no : Schema)
| SGuard (guards : Literals) (body : Schema).
Fixpoint evalSchema (s : Schema) (params : list nat) (x : Word) (indices : nat -> nat) : CNF :=
  match s with
  | SEmpty => [] | SClause vs => [evalLiterals vs params x indices]
  | SSeq a b => evalSchema a params x indices ++ evalSchema b params x indices
  | SForRange slot count body => flat_map
      (fun i => evalSchema body params x (setIndex indices slot i))
      (seq 0 (evalExpr count params x indices))
  | SIfLt a b yes no => if Nat.ltb (evalExpr a params x indices) (evalExpr b params x indices)
      then evalSchema yes params x indices else evalSchema no params x indices
  | SGuard guards body => map (fun c => evalLiterals guards params x indices ++ c)
      (evalSchema body params x indices)
  end.
Definition seqSchemas (ss : list Schema) : Schema := fold_right SSeq SEmpty ss.

"""


# Neutral constructor trees, rendered into both languages. All tableau data
# and all identifier arithmetic below have exactly one definition.
def node(op, *args):
    return (op, *args)


def const(n):
    return node("const", n)


def idx(n):
    return node("idx", n)


def add(a, b):
    return node("add", a, b)


def mul(a, b):
    return node("mul", a, b)


def sub(a, b):
    return node("sub", a, b)


def plus(a, n):
    return add(a, const(n))


def lits(*vs):
    return node("list", [node("pair", *v) for v in vs])


def clause(*vs):
    return node("clause", lits(*vs))


def seq(*ss):
    if not ss:
        return node("empty")
    if len(ss) == 1:
        return ss[0]
    return node("seq", ss[0], seq(*ss[1:]))


def loop(d, n, b):
    return node("forRange", d, n, b)


def call(name, *args):
    return node("call", name, *args)


def natadd(a, b):
    return node("natadd", a, b)


def tape(base, states, width, i):
    return add(add(add(base, states), width), mul(const(4), i))


def prefix(base, states, width, d, count):
    stride = plus(add(states, mul(const(5), width)), 1)
    return node(
        "range",
        d,
        count,
        add(add(base, mul(stride, idx(d))), add(states, mul(const(5), width))),
        True,
    )


DEFS = []


def define(name, params, body):
    DEFS.append((name, params, body))


d = "d"
d1 = natadd(d, 1)
d2 = natadd(d, 2)
b = "base"
z = "size"
w = "width"
st = "states"
nxt = "next"
h = "head"
prem = "prem"
i = idx(d)
j = idx(d1)


def eparam(k):
    return node("param", k)


define(
    "oneHotSchema",
    [(d, "Nat"), (b, "Expr"), (z, "Expr")],
    seq(
        node("clause", node("range", d, z, add(b, i), True)),
        loop(
            d,
            z,
            loop(
                d1,
                sub(sub(z, i), const(1)),
                clause((add(b, i), False), (add(plus(b, 1), add(i, j)), False)),
            ),
        ),
    ),
)
define(
    "certificateSchema",
    [(d, "Nat"), ("start", "Expr"), ("bound", "Expr")],
    seq(
        loop(
            d,
            "bound",
            seq(
                clause(
                    (plus(mul(const(2), add("start", i)), 1), False),
                    (mul(const(2), add("start", i)), True),
                ),
                clause(
                    (mul(const(2), plus(add("start", i), 1)), False),
                    (mul(const(2), add("start", i)), True),
                ),
            ),
        ),
        clause((mul(const(2), add("start", "bound")), False)),
    ),
)
define(
    "rowSchema",
    [(d, "Nat"), (b, "Expr"), (st, "Expr"), (w, "Expr")],
    seq(
        call("oneHotSchema", d, b, st),
        call("oneHotSchema", d, add(b, st), w),
        loop(d, w, call("oneHotSchema", d1, tape(b, st, w, i), const(4))),
    ),
)
define(
    "guardLiterals",
    [
        (b, "Expr"),
        (st, "Expr"),
        (w, "Expr"),
        ("q", "Nat"),
        (h, "Expr"),
        ("symbol", "Nat"),
    ],
    lits(
        (add(b, const("q")), False),
        (add(add(b, st), h), False),
        (add(tape(b, st, w, h), const("symbol")), False),
    ),
)
define(
    "copySchema",
    [
        (d, "Nat"),
        (prem, "Literals"),
        (b, "Expr"),
        (nxt, "Expr"),
        (st, "Expr"),
        (w, "Expr"),
        (h, "Expr"),
        ("write", "Nat"),
    ],
    loop(
        d,
        w,
        loop(
            d1,
            const(4),
            node(
                "guard",
                prem,
                clause(
                    (add(tape(b, st, w, i), j), False),
                    (
                        add(
                            tape(nxt, st, w, i),
                            node("selectEq", i, h, const("write"), j),
                        ),
                        True,
                    ),
                ),
            ),
        ),
    ),
)
define(
    "sourceSchema",
    [(b, "Expr"), ("position", "Expr")],
    seq(
        clause((mul(const(2), "position"), True), (b, True)),
        clause(
            (mul(const(2), "position"), False),
            (plus(mul(const(2), "position"), 1), True),
            (plus(b, 1), True),
        ),
        clause(
            (mul(const(2), "position"), False),
            (plus(mul(const(2), "position"), 1), False),
            (plus(b, 2), True),
        ),
    ),
)


# Static choices inspect only the fixed verifier table. Dynamic tests are
# syntax constructors, so the description is independent of the input.
def staticRange(n, v, body):
    return node("staticRange", n, v, body)


def states(m):
    return node("states", m)


def guarded(p, body):
    return node("guard", p, body)


def fail(p):
    return guarded(p, clause())


def whenLt(a, b, yes, no):
    return node("ifLt", a, b, yes, no)


def advance(h, dr):
    return node("direction", dr, sub(h, const(1)), plus(h, 1), h)


def inside(w, h, dr, yes, no):
    return node(
        "direction",
        dr,
        whenLt(const(0), h, yes, no),
        whenLt(plus(h, 1), w, yes, no),
        yes,
    )


st = const(states("m"))
pg = call("guardLiterals", b, st, w, "q", h, "symbol")
move = seq(
    guarded(
        pg,
        seq(
            clause((add(nxt, const("target")), True)),
            clause((add(add(nxt, st), advance(h, "dir")), True)),
        ),
    ),
    call("copySchema", d, pg, b, nxt, st, w, h, node("symbolIndex", "write")),
)
define(
    "instructionSchema",
    [
        (d, "Nat"),
        ("m", "Machine"),
        (b, "Expr"),
        (nxt, "Expr"),
        (w, "Expr"),
        ("q", "Nat"),
        (h, "Expr"),
        ("symbol", "Nat"),
    ],
    node(
        "instruction",
        "m",
        "q",
        "symbol",
        fail(pg),
        node(
            "staticLt",
            "target",
            states("m"),
            inside(w, h, "dir", move, fail(pg)),
            fail(pg),
        ),
    ),
)
define(
    "transitionSchema",
    [(d, "Nat"), ("m", "Machine"), (b, "Expr"), (nxt, "Expr"), (w, "Expr")],
    staticRange(
        states("m"),
        "q",
        loop(
            d,
            w,
            staticRange(
                4,
                "symbol",
                call("instructionSchema", d1, "m", b, nxt, w, "q", i, "symbol"),
            ),
        ),
    ),
)
define(
    "haltSchema",
    [(d, "Nat"), ("m", "Machine"), (b, "Expr"), (w, "Expr")],
    staticRange(
        states("m"),
        "q",
        loop(
            d,
            w,
            staticRange(
                4,
                "symbol",
                node(
                    "acceptInstruction",
                    "m",
                    "q",
                    "symbol",
                    node("empty"),
                    fail(call("guardLiterals", b, st, w, "q", i, "symbol")),
                ),
            ),
        ),
    ),
)
define(
    "successorSchema",
    [(d, "Nat"), ("m", "Machine"), (b, "Expr"), (nxt, "Expr"), (w, "Expr")],
    seq(
        call("rowSchema", d, b, st, w),
        call("rowSchema", d, nxt, st, w),
        call("transitionSchema", d, "m", b, nxt, w),
    ),
)
stride = plus(add(st, mul(const(5), w)), 1)
row = add(b, mul(stride, i))
stop = add(row, add(st, mul(const(5), w)))
define(
    "stopLiterals",
    [(d, "Nat"), (b, "Expr"), ("states", "Expr"), (w, "Expr"), ("count", "Expr")],
    prefix(b, "states", w, d, "count"),
)
define(
    "runSchema",
    [(d, "Nat"), ("m", "Machine"), (b, "Expr"), (w, "Expr"), ("fuel", "Expr")],
    seq(
        loop(
            d,
            "fuel",
            guarded(
                call("stopLiterals", d1, b, st, w, i),
                seq(
                    call("rowSchema", d1, row, st, w),
                    guarded(lits((stop, False)), call("haltSchema", d1, "m", row, w)),
                    guarded(
                        lits((stop, True)),
                        call("successorSchema", d1, "m", row, add(row, stride), w),
                    ),
                ),
            ),
        ),
        node("clause", call("stopLiterals", d, b, st, w, "fuel")),
    ),
)

n = eparam(0)
B = eparam(1)
T = eparam(2)
W = eparam(3)
base = plus(mul(const(2), B), 1)
tape0 = add(add(base, st), W)


def blankSchema(start, count):
    return loop(0, count, clause((add(tape0, mul(const(4), add(start, idx(0)))), True)))


bits = loop(
    0,
    n,
    clause(
        (
            add(
                add(tape0, mul(const(4), add(T, idx(0)))), plus(node("bit", idx(0)), 1)
            ),
            True,
        )
    ),
)
pairedTail = seq(
    clause((plus(add(tape0, mul(const(4), add(T, n))), 3), True)),
    loop(
        0,
        B,
        call(
            "sourceSchema",
            add(tape0, mul(const(4), add(plus(add(T, n), 1), idx(0)))),
            idx(0),
        ),
    ),
    blankSchema(add(plus(add(T, n), 1), B), sub(sub(sub(sub(W, T), n), const(1)), B)),
)
define(
    "initialSchema",
    [("m", "Machine"), ("paired", "Bool")],
    seq(
        call("rowSchema", 0, base, st, W),
        clause((base, True)),
        clause((add(add(base, st), T), True)),
        blankSchema(const(0), T),
        bits,
        node(
            "staticBool",
            "paired",
            pairedTail,
            blankSchema(add(T, n), sub(sub(W, T), n)),
        ),
    ),
)
define(
    "machineSchema",
    [("m", "Machine"), ("paired", "Bool")],
    seq(
        call("certificateSchema", 0, const(0), B),
        call("initialSchema", "m", "paired"),
        call("runSchema", 0, "m", base, W, T),
    ),
)
define(
    "tableauSchema",
    [("np", "ClassNP")],
    node(
        "verifier",
        "np",
        call("machineSchema", "m", False),
        call("machineSchema", "m", True),
    ),
)


def render(t, lang):
    if isinstance(t, bool):
        return str(t).lower()
    if isinstance(t, (int, str)):
        return str(t)
    if isinstance(t, list):
        sep = ", " if lang == "lean" else "; "
        return "[" + sep.join(render(x, lang) for x in t) + "]"
    op, *a = t
    if op == "pair":
        return "(" + render(a[0], lang) + ", " + render(a[1], lang) + ")"
    if op == "natadd":
        return "(" + render(a[0], lang) + " + " + render(a[1], lang) + ")"
    if op == "call":
        return "(" + a[0] + " " + " ".join(render(x, lang) for x in a[1:]) + ")"
    if op == "states":
        return (
            f"({a[0]}.program.length)"
            if lang == "lean"
            else f"(length (program {a[0]}))"
        )
    if op == "symbolIndex":
        return f"({a[0]}.index)" if lang == "lean" else f"(symbolIndex {a[0]})"
    if op == "staticRange":
        count, v, body = a
        return (
            f"(seqSchemas ((List.range {render(count,lang)}).map fun {v} => {render(body,lang)}))"
            if lang == "lean"
            else f"(seqSchemas (map (fun {v} => {render(body,lang)}) (seq 0 {render(count,lang)})))"
        )
    if op in ("staticLt", "staticBool"):
        if op == "staticLt":
            aa, bb, yes, no = a
            condition = (
                f"{render(aa,lang)} < {render(bb,lang)}"
                if lang == "lean"
                else f"Nat.ltb {render(aa,lang)} {render(bb,lang)}"
            )
        else:
            condition, yes, no = a
        return f"(if {condition} then {render(yes,lang)} else {render(no,lang)})"
    if op == "instruction":
        m, q, s, halt, move = a
        return (
            f"(match {m}.instruction {q} (symbolOfIndex {s}) with | .halt _ => {render(halt,lang)} | .move target write dir => {render(move,lang)})"
            if lang == "lean"
            else f"(match instruction {m} {q} (symbolOfIndex {s}) with | halt _ => {render(halt,lang)} | move target write dir => {render(move,lang)} end)"
        )
    if op == "acceptInstruction":
        m, q, s, yes, no = a
        return (
            f"(if {m}.instruction {q} (symbolOfIndex {s}) = .halt true then {render(yes,lang)} else {render(no,lang)})"
            if lang == "lean"
            else f"(match instruction {m} {q} (symbolOfIndex {s}) with | halt true => {render(yes,lang)} | _ => {render(no,lang)} end)"
        )
    if op == "direction":
        dr, left, right, stay = a
        return (
            f"(match {dr} with | .left => {render(left,lang)} | .right => {render(right,lang)} | .stay => {render(stay,lang)})"
            if lang == "lean"
            else f"(match {dr} with | left => {render(left,lang)} | right => {render(right,lang)} | stay => {render(stay,lang)} end)"
        )
    if op == "verifier":
        np, ignore, paired = a
        return (
            f"(match {np}.verifier with | .ignoreCertificate m => {render(ignore,lang)} | .paired m => {render(paired,lang)})"
            if lang == "lean"
            else f"(match np_verifier {np} with | ignoreCertificate m => {render(ignore,lang)} | paired m => {render(paired,lang)} end)"
        )
    # Plain pairs in literal lists are (Expr, Bool), not constructor nodes.
    if not isinstance(op, str):
        return "(" + render(op, lang) + ", " + render(a[0], lang) + ")"
    names = {
        "const": "EConst",
        "param": "EParam",
        "idx": "EIdx",
        "bit": "EBit",
        "add": "EAdd",
        "mul": "EMul",
        "sub": "ESub",
        "selectEq": "ESelectEq",
        "list": "LList",
        "append": "LAppend",
        "range": "LRange",
        "empty": "SEmpty",
        "clause": "SClause",
        "seq": "SSeq",
        "forRange": "SForRange",
        "ifLt": "SIfLt",
        "guard": "SGuard",
    }
    name = "." + op if lang == "lean" else names[op]
    return "(" + name + (" " + " ".join(render(x, lang) for x in a) if a else "") + ")"


def declarations(lang):
    out = LEAN_CORE if lang == "lean" else ROCQ_CORE
    for name, params, body in DEFS:
        typ = "Schema" if name.endswith("Schema") else "Literals"
        args = " ".join(
            f'({n} : {"nat" if lang=="rocq" and t=="Nat" else ("bool" if lang=="rocq" and t=="Bool" else t)})'
            for n, t in params
        )
        out += f'{"def" if lang=="lean" else "Definition"} {name} {args} : {typ} :=\n  {render(body,lang)}{chr(10) if lang=="lean" else "."+chr(10)}\n'
    out += (
        "def tableauParams (np : ClassNP) (n : Nat) : List Nat :=\n  [n, np.certBound.eval n, maxClock np n, windowWidth np n]\n\n"
        if lang == "lean"
        else "Definition tableauParams (np : ClassNP) (n : nat) : list nat :=\n  [n; evalPoly (np_certBound np) n; maxClock np n; windowWidth np n].\n\n"
    )
    return out


def generate(check=False):
    stale = []
    for lang, ext in [("lean", "lean"), ("rocq", "v")]:
        p = ROOT / f"proofs/experiments/issue624/{lang}/Schema.{ext}"
        marker = MARKERS[lang]
        old = p.read_text() if p.exists() else ""
        tail = (
            old.split(marker, 1)[1]
            if marker in old
            else ("\nend Issue624.Schema\n" if lang == "lean" else "\nEnd Schema.\n")
        )
        new = declarations(lang) + marker + tail
        if old != new:
            stale.append(str(p.relative_to(ROOT)))
            if not check:
                p.write_text(new)
    if check and stale:
        raise SystemExit("Generated schema data differs: " + ", ".join(stale))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    generate(parser.parse_args().check)
