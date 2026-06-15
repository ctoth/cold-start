"""A tiny mutation tester for the trusted core (Windows-native; mutmut needs WSL).

Injects one mutation at a time into a target module, runs a fast test subset, and
reports which mutants SURVIVED -- a surviving mutant is a deliberately broken
checker that no test noticed, i.e. a concrete blind spot. Restores the original
on exit no matter what.

Usage:  uv run python tools/mutate.py cold_start/checker.py
"""

from __future__ import annotations

import ast
import copy
import subprocess
import sys
from pathlib import Path

# Fast, mostly-deterministic tests that exercise the checker hard. Survivors are
# re-checked against the full suite by hand (there should be few).
TEST_CMD = [
    "uv", "run", "pytest", "-q", "-x",
    "tests/test_checker.py", "tests/test_quantifiers.py", "tests/test_logic.py",
    "tests/test_sorts.py", "tests/test_rings.py",
]

CMP_SWAP = {
    ast.Is: ast.IsNot, ast.IsNot: ast.Is, ast.Eq: ast.NotEq, ast.NotEq: ast.Eq,
    ast.Lt: ast.LtE, ast.LtE: ast.Lt, ast.Gt: ast.GtE, ast.GtE: ast.Gt,
    ast.In: ast.NotIn, ast.NotIn: ast.In,
}
BOOL_SWAP = {ast.And: ast.Or, ast.Or: ast.And}


def _build(tree: ast.AST, target: int):
    """Return (mutated_tree_or_None, description, total_sites). If target is in
    range, that site is mutated; otherwise nothing is (used to count)."""
    counter = [0]
    desc: list[str] = []

    class T(ast.NodeTransformer):
        def visit_Compare(self, node):
            self.generic_visit(node)
            for i, op in enumerate(node.ops):
                if type(op) in CMP_SWAP:
                    if counter[0] == target:
                        old = type(op).__name__
                        node.ops[i] = CMP_SWAP[type(op)]()
                        desc.append(f"line {node.lineno}: {old} -> {type(node.ops[i]).__name__}")
                    counter[0] += 1
            return node

        def visit_BoolOp(self, node):
            self.generic_visit(node)
            if type(node.op) in BOOL_SWAP:
                if counter[0] == target:
                    node.op = BOOL_SWAP[type(node.op)]()
                    desc.append(f"line {node.lineno}: {type(node.op).__name__} (and<->or)")
                counter[0] += 1
            return node

        def visit_UnaryOp(self, node):
            self.generic_visit(node)
            if isinstance(node.op, ast.Not):
                if counter[0] == target:
                    desc.append(f"line {node.lineno}: drop `not`")
                    counter[0] += 1
                    return node.operand
                counter[0] += 1
            return node

    new = T().visit(copy.deepcopy(tree))
    ast.fix_missing_locations(new)
    return new, (desc[0] if desc else ""), counter[0]


def main(path: str) -> int:
    target = Path(path)
    original = target.read_text()
    tree = ast.parse(original)
    _, _, total = _build(tree, -1)
    print(f"{total} mutation sites in {path}\n")
    survivors = []
    try:
        for k in range(total):
            mutant, desc, _ = _build(tree, k)
            target.write_text(ast.unparse(mutant))
            r = subprocess.run(TEST_CMD, capture_output=True)
            if r.returncode == 0:
                survivors.append(desc)
                print(f"  SURVIVED  {desc}")
            else:
                print(f"  killed    {desc}")
    finally:
        target.write_text(original)
    print(f"\n{len(survivors)}/{total} survived")
    for d in survivors:
        print("  SURVIVOR:", d)
    return 1 if survivors else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1] if len(sys.argv) > 1 else "cold_start/checker.py"))
