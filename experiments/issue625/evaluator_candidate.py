#!/usr/bin/env python3
"""Executable counterpart of the certified single-tape circuit evaluator.

The table uses exactly Complexity's four symbols and charged instructions.
It never calls the decoder or evaluator. Unary indices are counted by shuttling
between one marked gate and a marked wire-list cursor. Each gate's output is
appended to the certificate region only after both lookups succeed.

The paired CircuitVerifier modules prove this table correct for all inputs.
This bounded interpreter is used only for concrete regression traces.
"""

import argparse
from collections import deque
from dataclasses import dataclass
import json

BLANK, ZERO, ONE, SEPARATOR = range(4)
LEFT, STAY, RIGHT = -1, 0, 1


@dataclass(frozen=True)
class Halt:
    answer: bool


@dataclass(frozen=True)
class Move:
    state: str
    write: int
    direction: int


@dataclass(frozen=True)
class Result:
    answer: bool
    steps: int
    states: int


def instruction_table():
    table = {}

    def put(state, symbol, instruction):
        if (state, symbol) in table:
            raise ValueError(f'duplicate instruction: {state}, {symbol}')
        table[state, symbol] = instruction

    def move(state, symbol, target, direction, write=None):
        put(state, symbol, Move(target, symbol if write is None else write, direction))

    def scan(state, symbols, direction, target=None):
        for symbol in symbols:
            move(state, symbol, state if target is None else target, direction)

    bits = (ZERO, ONE)
    phases = ('header', 'marker', 'first', 'second', 'done', 'bad')
    syntax = {
        'header': ('marker', 'header'), 'marker': ('done', 'first'),
        'first': ('second', 'first'), 'second': ('marker', 'second'),
        'done': ('bad', 'bad'), 'bad': ('bad', 'bad'),
    }
    for phase in phases:
        for bit, target in zip(bits, syntax[phase]):
            move('syntax_' + phase, bit, 'syntax_' + target, RIGHT)
        if phase == 'done':
            move('syntax_' + phase, SEPARATOR, 'start_left', LEFT)
    scan('start_left', bits, LEFT)
    move('start_left', BLANK, 'count_first', RIGHT)

    # Match the unary header with certificate length, preserving every bit.
    # The first count creates a cursor, the others advance it. A cursor uses
    # blank for false and separator for true. No other wire cell is marked.
    for mode in ('first', 'next'):
        move('count_' + mode, ONE, 'count_seek_' + mode, RIGHT, SEPARATOR)
        move('count_' + mode, ZERO, 'count_seek_' + ('empty' if mode == 'first' else 'end'), RIGHT)
    for mode in ('first', 'next', 'empty', 'end'):
        scan('count_seek_' + mode, bits, RIGHT)
        move('count_seek_' + mode, SEPARATOR, 'count_cert_' + mode, RIGHT)
    for bit in bits:
        move('count_cert_first', bit, 'count_back_sep', LEFT, BLANK if bit == ZERO else SEPARATOR)
        move('count_mark_next', bit, 'count_back_sep', LEFT, BLANK if bit == ZERO else SEPARATOR)
    for mode in ('next', 'end'):
        scan('count_cert_' + mode, bits, RIGHT)
        target = 'count_mark_next' if mode == 'next' else 'count_check_end'
        move('count_cert_' + mode, BLANK, target, RIGHT, ZERO)
        move('count_cert_' + mode, SEPARATOR, target, RIGHT, ONE)
    move('count_cert_empty', BLANK, 'count_finish_sep', LEFT)
    move('count_check_end', BLANK, 'count_finish_sep', LEFT)
    scan('count_back_sep', bits, LEFT)
    move('count_back_sep', SEPARATOR, 'count_back_left', LEFT)
    scan('count_back_left', (*bits, SEPARATOR), LEFT)
    move('count_back_left', BLANK, 'count_skip', RIGHT)
    move('count_skip', SEPARATOR, 'count_skip', RIGHT)
    for bit in bits:
        move('count_skip', bit, 'count_next', STAY)
    scan('count_finish_sep', bits, LEFT)
    move('count_finish_sep', SEPARATOR, 'count_restore_left', LEFT)
    scan('count_restore_left', (*bits, SEPARATOR), LEFT)
    move('count_restore_left', BLANK, 'count_restore', RIGHT)
    move('count_restore', SEPARATOR, 'count_restore', RIGHT, ONE)
    move('count_restore', ZERO, 'gate', RIGHT)

    # The current gate marker becomes blank. The suffix after the current
    # unary counter is unmodified, so its first separator is the input/cert
    # boundary. Used unary ticks lie to the left of the head.
    move('gate', ONE, 'lookup_first_init', RIGHT, BLANK)
    move('gate', ZERO, 'finish_boundary', RIGHT)

    for kind, first_value in (('first', None), ('second_false', False), ('second_true', True)):
        prefix = 'lookup_' + kind
        scan(prefix + '_init', bits, RIGHT)
        move(prefix + '_init', SEPARATOR, prefix + '_mark_initial', RIGHT)
        for bit in bits:
            move(prefix + '_mark_initial', bit, prefix + '_back_sep', LEFT,
                 BLANK if bit == ZERO else SEPARATOR)
        scan(prefix + '_back_sep', bits, LEFT)
        move(prefix + '_back_sep', SEPARATOR, prefix + '_back_gate', LEFT)
        scan(prefix + '_back_gate', (*bits, SEPARATOR), LEFT)
        move(prefix + '_back_gate', BLANK,
             prefix + ('_unary' if first_value is None else '_skip_first'), RIGHT)
        if first_value is not None:
            move(prefix + '_skip_first', ONE, prefix + '_skip_first', RIGHT)
            move(prefix + '_skip_first', ZERO, prefix + '_unary', RIGHT)
        move(prefix + '_unary', SEPARATOR, prefix + '_unary', RIGHT)
        move(prefix + '_unary', ONE, prefix + '_seek_increment', RIGHT, SEPARATOR)
        move(prefix + '_unary', ZERO, prefix + '_seek_read', RIGHT)
        for operation in ('increment', 'read'):
            scan(prefix + '_seek_' + operation, bits, RIGHT)
            move(prefix + '_seek_' + operation, SEPARATOR, prefix + '_cursor_' + operation, RIGHT)
            scan(prefix + '_cursor_' + operation, bits, RIGHT)
        for cursor, bit in ((BLANK, ZERO), (SEPARATOR, ONE)):
            move(prefix + '_cursor_increment', cursor, prefix + '_mark_next', RIGHT, bit)
            value = bit == ONE
            if first_value is None:
                target = 'first_restore_' + str(value).lower()
            else:
                target = 'second_restore_' + str(not (first_value and value)).lower()
            move(prefix + '_cursor_read', cursor, target + '_sep', LEFT, bit)
        for bit in bits:
            move(prefix + '_mark_next', bit, prefix + '_back_sep', LEFT,
                 BLANK if bit == ZERO else SEPARATOR)

    for value in (False, True):
        suffix = str(value).lower()
        for which in ('first', 'second'):
            prefix = which + '_restore_' + suffix
            scan(prefix + '_sep', bits, LEFT)
            move(prefix + '_sep', SEPARATOR, prefix + '_gate', LEFT)
            scan(prefix + '_gate', (*bits, SEPARATOR), LEFT)
            move(prefix + '_gate', BLANK, prefix + ('_unary' if which == 'first' else '_skip_first'), RIGHT)
            if which == 'second':
                move(prefix + '_skip_first', ONE, prefix + '_skip_first', RIGHT)
                move(prefix + '_skip_first', ZERO, prefix + '_unary', RIGHT)
            move(prefix + '_unary', SEPARATOR, prefix + '_unary', RIGHT, ONE)
            if which == 'first':
                move(prefix + '_unary', ZERO, 'lookup_second_' + suffix + '_init', RIGHT)
            else:
                move(prefix + '_unary', ZERO, 'append_' + suffix + '_sep', RIGHT)
        scan('append_' + suffix + '_sep', bits, RIGHT)
        move('append_' + suffix + '_sep', SEPARATOR, 'append_' + suffix + '_end', RIGHT)
        scan('append_' + suffix + '_end', bits, RIGHT)
        move('append_' + suffix + '_end', BLANK, 'append_back_sep', LEFT, ONE if value else ZERO)
    scan('append_back_sep', bits, LEFT)
    move('append_back_sep', SEPARATOR, 'append_back_gate', LEFT)
    scan('append_back_gate', bits, LEFT)
    move('append_back_gate', BLANK, 'advance_first', RIGHT, ONE)
    move('advance_first', ONE, 'advance_first', RIGHT)
    move('advance_first', ZERO, 'advance_second', RIGHT)
    move('advance_second', ONE, 'advance_second', RIGHT)
    move('advance_second', ZERO, 'gate', RIGHT)

    move('finish_boundary', SEPARATOR, 'finish_false', RIGHT)
    for value in (False, True):
        state = 'finish_' + str(value).lower()
        move(state, ZERO, 'finish_false', RIGHT)
        move(state, ONE, 'finish_true', RIGHT)
        put(state, BLANK, Halt(value))

    states = ['syntax_header'] + sorted({q for q, _ in table} - {'syntax_header'})
    targets = {i.state for i in table.values() if isinstance(i, Move)}
    missing = targets - set(states)
    if missing:
        raise ValueError(f'undefined states: {missing}')
    return states, [[table.get((state, symbol), Halt(False)) for symbol in range(4)] for state in states]


STATES, TABLE = instruction_table()
STATE_INDEX = {state: index for index, state in enumerate(STATES)}


def run_machine(word, certificate, *, trace=False, step_limit=None, program=None):
    """Follow Complexity.moveHead exactly, including explicit blank cells."""
    program = TABLE if program is None else program
    symbols = [ONE if bit else ZERO for bit in word] + [SEPARATOR] + [ONE if bit else ZERO for bit in certificate]
    left, head, right = [], symbols[0], deque(symbols[1:])
    state = 0
    if step_limit is None:
        step_limit = 128 * (len(word) + len(certificate) + 2) ** 2
    for steps in range(1, step_limit + 1):
        instruction = program[state][head]
        if trace:
            print(json.dumps({'step': steps, 'state': STATES[state], 'left': left,
                              'head': head, 'right': list(right)}, separators=(',', ':')))
        if isinstance(instruction, Halt):
            return Result(instruction.answer, steps, len(STATES))
        state = STATE_INDEX[instruction.state]
        if instruction.direction == LEFT:
            right.appendleft(instruction.write)
            head = left.pop() if left else BLANK
        elif instruction.direction == RIGHT:
            left.append(instruction.write)
            head = right.popleft() if right else BLANK
        else:
            head = instruction.write
    raise RuntimeError(f'finite instruction budget exceeded: {step_limit}, {STATES[state]}')


def enc_circuit(n, gates):
    word = [True] * n + [False]
    for i, j in gates:
        word += [True] + [True] * i + [False] + [True] * j + [False]
    return word + [False]


def verify_circuit(word, certificate):
    """Independent executable version of Idea41.verifyCircuit, no table use."""
    position = 0

    def natural():
        nonlocal position
        value = 0
        while position < len(word) and word[position]:
            position += 1
            value += 1
        if position == len(word):
            raise ValueError('unterminated unary index')
        position += 1
        return value

    try:
        n = natural()
        gates = []
        while position < len(word) and word[position]:
            position += 1
            gates.append((natural(), natural()))
        if position != len(word) - 1 or word[position]:
            return False
    except (ValueError, IndexError):
        return False
    if len(certificate) != n:
        return False
    wires = list(certificate)
    for i, j in gates:
        if i >= len(wires) or j >= len(wires):
            return False
        wires.append(not (wires[i] and wires[j]))
    return wires[-1] if wires else False


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--word', default='101000', help='raw instance bits')
    parser.add_argument('--certificate', default='1', help='certificate bits')
    parser.add_argument('--trace', action='store_true', help='emit every charged instruction')
    args = parser.parse_args()
    if any(bit not in '01' for bit in args.word + args.certificate):
        parser.error('words must contain only 0 and 1')
    word = [bit == '1' for bit in args.word]
    certificate = [bit == '1' for bit in args.certificate]
    result = run_machine(word, certificate, trace=args.trace)
    print(result)
    print('specification:', verify_circuit(word, certificate))


if __name__ == '__main__':
    main()
