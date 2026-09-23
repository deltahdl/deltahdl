import ast
import operator
import os
import re
import sys
from pathlib import Path
from typing import Any, Callable

REPO_ROOT = Path(__file__).resolve().parents[3]
BINARY = REPO_ROOT / "build" / "src" / "deltahdl"

_NO_COLOR = (
    not sys.stdout.isatty() and not os.environ.get("CI")
) or os.environ.get("NO_COLOR")

GREEN = "" if _NO_COLOR else "\033[32m"
RED = "" if _NO_COLOR else "\033[31m"
RESET = "" if _NO_COLOR else "\033[0m"


def check_binary() -> None:
    if not BINARY.exists():
        print(f"error: binary not found at {BINARY}", file=sys.stderr)
        sys.exit(1)


def print_result(passed: bool, name: str) -> None:
    if passed:
        print(f"  {GREEN}PASS{RESET}: {name}", flush=True)
    else:
        print(f"  {RED}FAIL{RESET}: {name}", flush=True)


def parse_metadata(path: str) -> dict[str, str]:
    text = Path(path).read_text(encoding="utf-8")
    match = re.search(r"/\*(.*?)\*/", text, re.DOTALL)
    if not match:
        return {}
    metadata: dict[str, str] = {}
    for line in match.group(1).splitlines():
        m = re.match(r"\s*:(\w+):\s*(.*)", line)
        if m:
            metadata[m.group(1)] = m.group(2).strip()
    return metadata


_UNARY_OPS: dict[type[ast.unaryop], Callable[[Any], Any]] = {
    ast.Not: operator.not_,
    ast.USub: operator.neg,
    ast.UAdd: operator.pos,
    ast.Invert: operator.invert,
}

_BINARY_OPS: dict[type[ast.operator], Callable[[Any, Any], Any]] = {
    ast.Add: operator.add,
    ast.Sub: operator.sub,
    ast.Mult: operator.mul,
    ast.FloorDiv: operator.floordiv,
    ast.Mod: operator.mod,
    ast.Pow: operator.pow,
    ast.LShift: operator.lshift,
    ast.RShift: operator.rshift,
    ast.BitAnd: operator.and_,
    ast.BitOr: operator.or_,
    ast.BitXor: operator.xor,
}

_COMPARE_OPS: dict[type[ast.cmpop], Callable[[Any, Any], bool]] = {
    ast.Eq: operator.eq,
    ast.NotEq: operator.ne,
    ast.Lt: operator.lt,
    ast.LtE: operator.le,
    ast.Gt: operator.gt,
    ast.GtE: operator.ge,
    ast.In: lambda a, b: operator.contains(b, a),
    ast.NotIn: lambda a, b: not operator.contains(b, a),
}


def _eval_compare(node: ast.Compare) -> bool:
    left = eval_node(node.left)
    for op, comp in zip(node.ops, node.comparators):
        right = eval_node(comp)
        if not _COMPARE_OPS[type(op)](left, right):
            return False
        left = right
    return True


def eval_node(node: ast.AST) -> Any:
    if isinstance(node, ast.Constant):
        return node.value
    if isinstance(node, ast.Compare):
        return _eval_compare(node)
    if isinstance(node, ast.BoolOp):
        vals = [eval_node(v) for v in node.values]
        return all(vals) if isinstance(node.op, ast.And) else any(vals)
    if isinstance(node, ast.UnaryOp) and type(node.op) in _UNARY_OPS:
        return _UNARY_OPS[type(node.op)](eval_node(node.operand))
    if isinstance(node, ast.BinOp) and type(node.op) in _BINARY_OPS:
        return _BINARY_OPS[type(node.op)](eval_node(node.left), eval_node(node.right))
    raise ValueError(f"Unsupported node: {type(node).__name__}")


def try_string_equality(expr: str) -> bool | None:
    m = re.match(r"\(\s*'(.*)'\s*==\s*'(.*)'\s*\)$", expr)
    if m:
        return m.group(1) == m.group(2)
    return None


def check_assertions(stdout: str) -> tuple[bool, str]:
    for line in stdout.splitlines():
        match = re.search(r":assert:\s*(.*)", line)
        if not match:
            continue
        expr = match.group(1).strip().replace("\0", "")
        try:
            tree = ast.parse(expr, mode="eval")
            if not eval_node(tree.body):
                return False, f"Assertion failed: {expr}"
        except (SyntaxError, ValueError):
            result = try_string_equality(expr)
            if result is None:
                return False, f"Assertion parse error: {expr}"
            if not result:
                return False, f"Assertion failed: {expr}"
    return True, ""


_SUBCLAUSE_RE = re.compile(r"\(§(\d+(?:\.\d+)*)\)")


def reported_subclauses(stderr: str) -> list[str]:
    return _SUBCLAUSE_RE.findall(stderr)


def subclause_is_within(reported: str, clause: str) -> bool:
    clause_parts = clause.split(".")
    return reported.split(".")[: len(clause_parts)] == clause_parts
