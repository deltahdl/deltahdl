"""Finds a reserved keyword written as a name in a test's SystemVerilog.

A test that hands the tool a source is asserting something about how the source
is read. If the source does not parse, the tool reads nothing out of it, and
whether the test notices depends entirely on what it went on to assert. A test
expecting something to appear fails loudly, which is the good case. A test
expecting something *not* to appear -- no cell in either library, no warning, no
binding -- is satisfied by an input that never happened, and passes for as long
as it stands while covering the rule it never exercised.

Table B.1 reserves about two hundred and fifty words, and the ordinary English
among them are exactly the ones an author reaches for: `cell` for a cell,
`before` for the state before an edit, `time`, `edge`, `final`, `cover`,
`local`, `large`, `context`, `bind`, `new`, `type`, `use`, `table`, `event`. A
declaration naming one of those is not a declaration, and nothing in the tree
says so.

The scan reads the SystemVerilog embedded in a test source's string literals
and reports a declaration whose name is reserved. It reads literals one at a
time rather than the file as a whole, so that the C++ around them -- where
`int before = 0;` is perfectly good -- is never mistaken for a design.

What it cannot see is a name built at run time out of pieces, since only the
pieces are written down. That is the limit of reading a source rather than
running it, and it is why this scan is a floor rather than a proof.
"""

import re

# Table B.1 of IEEE 1800-2023, in full. The scan is only as good as this list,
# so it is transcribed from the standard rather than from any keyword table this
# repository holds for its own purposes: a lexer that has forgotten a word would
# otherwise excuse every test that uses it.
RESERVED = frozenset({
    "accept_on", "alias", "always", "always_comb", "always_ff", "always_latch",
    "and", "assert", "assign", "assume", "automatic", "before", "begin", "bind",
    "bins", "binsof", "bit", "break", "buf", "bufif0", "bufif1", "byte", "case",
    "casex", "casez", "cell", "chandle", "checker", "class", "clocking", "cmos",
    "config", "const", "constraint", "context", "continue", "cover",
    "covergroup", "coverpoint", "cross", "deassign", "default", "defparam",
    "design", "disable", "dist", "do", "edge", "else", "end", "endcase",
    "endchecker", "endclass", "endclocking", "endconfig", "endfunction",
    "endgenerate", "endgroup", "endinterface", "endmodule", "endpackage",
    "endprimitive", "endprogram", "endproperty", "endsequence", "endspecify",
    "endtable", "endtask", "enum", "event", "eventually", "expect", "export",
    "extends", "extern", "final", "first_match", "for", "force", "foreach",
    "forever", "fork", "forkjoin", "function", "generate", "genvar", "global",
    "highz0", "highz1", "if", "iff", "ifnone", "ignore_bins", "illegal_bins",
    "implements", "implies", "import", "incdir", "include", "initial", "inout",
    "input", "inside", "instance", "int", "integer", "interconnect",
    "interface", "intersect", "join", "join_any", "join_none", "large", "let",
    "liblist", "library", "local", "localparam", "logic", "longint",
    "macromodule", "matches", "medium", "modport", "module", "nand", "negedge",
    "nettype", "new", "nexttime", "nmos", "nor", "noshowcancelled", "not",
    "notif0", "notif1", "null", "or", "output", "package", "packed",
    "parameter", "pmos", "posedge", "primitive", "priority", "program",
    "property", "protected", "pull0", "pull1", "pulldown", "pullup",
    "pulsestyle_ondetect", "pulsestyle_onevent", "pure", "rand", "randc",
    "randcase", "randsequence", "rcmos", "real", "realtime", "ref", "reg",
    "reject_on", "release", "repeat", "restrict", "return", "rnmos", "rpmos",
    "rtran", "rtranif0", "rtranif1", "s_always", "s_eventually", "s_nexttime",
    "s_until", "s_until_with", "scalared", "sequence", "shortint", "shortreal",
    "showcancelled", "signed", "small", "soft", "solve", "specify", "specparam",
    "static", "string", "strong", "strong0", "strong1", "struct", "super",
    "supply0", "supply1", "sync_accept_on", "sync_reject_on", "table", "tagged",
    "task", "this", "throughout", "time", "timeprecision", "timeunit", "tran",
    "tranif0", "tranif1", "tri", "tri0", "tri1", "triand", "trior", "trireg",
    "type", "typedef", "union", "unique", "unique0", "unsigned", "until",
    "until_with", "untyped", "use", "uwire", "var", "vectored", "virtual",
    "void", "wait", "wait_order", "wand", "weak", "weak0", "weak1", "while",
    "wildcard", "wire", "with", "within", "wor", "xnor", "xor",
})

# The keywords after which the source is naming the thing it declares.
DECLARING = (
    "checker", "config", "genvar", "interface", "macromodule", "module",
    "package", "primitive", "program", "wire",
)

# The words the standard allows to stand between one of those keywords and the
# name. §23.2 and §26.2 let a lifetime -- `static` or `automatic` -- precede a
# module, program or package name; §8.26 writes an interface class as
# `interface class`; §6.7 lets a net state a data type and its signing before
# the name. In that position none of them is a name, so the scan passes over
# them and reads on rather than reporting them as one.
PASSED_OVER = (
    "automatic", "class", "logic", "reg", "signed", "static", "unsigned",
)

_LITERAL = re.compile(r'"((?:[^"\\]|\\.)*)"')
_DECLARATION = re.compile(
    r"\b(" + "|".join(DECLARING) + r")\s+"
    r"(?:(?:" + "|".join(PASSED_OVER) + r")\s+)*"
    r"([A-Za-z_][A-Za-z0-9_$]*)"
)


def literals_of(source: str) -> list[str]:
    """Return the contents of every string literal in the C++ *source*."""
    return _LITERAL.findall(source)


def declarations_in(text: str) -> list[tuple[str, str]]:
    """Return the (keyword, name) pairs *text* declares."""
    return [(m.group(1), m.group(2)) for m in _DECLARATION.finditer(text)]


def reserved_declarations(source: str) -> list[str]:
    """Name what the C++ *source* declares in SystemVerilog and may not."""
    return [
        f"{keyword} {name}"
        for literal in literals_of(source)
        for keyword, name in declarations_in(literal)
        if name in RESERVED
    ]
