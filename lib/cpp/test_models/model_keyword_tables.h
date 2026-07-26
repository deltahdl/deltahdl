#pragma once

#include "lexer/token.h"

// The reserved-keyword tables of §22.14, transcribed once. A version_specifier
// given to `begin_keywords names one of these tables, and each table is defined
// as what it adds to the ones it includes, so a test for a later version reads
// several of them together.
//
// Every §22.14 test file used to carry its own transcription of the tables it
// needed. Holding them once means two tests cannot disagree about what the
// standard reserves.

// Table 22-1 -- the reserved keywords of IEEE 1364-1995, the oldest
// version_specifier `begin_keywords accepts.
inline constexpr const char* kTable221[] = {
    "always",    "and",          "assign",     "begin",     "buf",
    "bufif0",    "bufif1",       "case",       "casex",     "casez",
    "cmos",      "deassign",     "default",    "defparam",  "disable",
    "edge",      "else",         "end",        "endcase",   "endfunction",
    "endmodule", "endprimitive", "endspecify", "endtable",  "endtask",
    "event",     "for",          "force",      "forever",   "fork",
    "function",  "highz0",       "highz1",     "if",        "ifnone",
    "initial",   "inout",        "input",      "integer",   "join",
    "large",     "macromodule",  "medium",     "module",    "nand",
    "negedge",   "nmos",         "nor",        "not",       "notif0",
    "notif1",    "or",           "output",     "parameter", "pmos",
    "posedge",   "primitive",    "pull0",      "pull1",     "pulldown",
    "pullup",    "rcmos",        "real",       "realtime",  "reg",
    "release",   "repeat",       "rnmos",      "rpmos",     "rtran",
    "rtranif0",  "rtranif1",     "scalared",   "small",     "specify",
    "specparam", "strong0",      "strong1",    "supply0",   "supply1",
    "table",     "task",         "time",       "tran",      "tranif0",
    "tranif1",   "tri",          "tri0",       "tri1",      "triand",
    "trior",     "trireg",       "vectored",   "wait",      "wand",
    "weak0",     "weak1",        "while",      "wire",      "wor",
    "xnor",      "xor",
};

// Table 22-2 -- what IEEE 1364-2001 reserves over Table 22-1.
inline constexpr const char* kTable222Words[] = {
    "automatic",
    "cell",
    "config",
    "design",
    "endconfig",
    "endgenerate",
    "generate",
    "genvar",
    "incdir",
    "include",
    "instance",
    "liblist",
    "library",
    "localparam",
    "noshowcancelled",
    "pulsestyle_ondetect",
    "pulsestyle_onevent",
    "showcancelled",
    "signed",
    "unsigned",
    "use",
};

// Table 22-3 -- what IEEE 1364-2001-noconfig withholds relative to
// 1364-2001: the configuration keywords it does not reserve.
inline constexpr const char* kTable223[] = {
    "uwire",
};

// Table 22-4 -- what IEEE 1364-2005 and SystemVerilog reserve over the
// Verilog tables above.
inline constexpr const char* kTable224Words[] = {
    "alias",         "always_comb",  "always_ff",    "always_latch",
    "assert",        "assume",       "before",       "bind",
    "bins",          "binsof",       "bit",          "break",
    "byte",          "chandle",      "class",        "clocking",
    "const",         "constraint",   "context",      "continue",
    "cover",         "covergroup",   "coverpoint",   "cross",
    "dist",          "do",           "endclass",     "endclocking",
    "endgroup",      "endinterface", "endpackage",   "endprogram",
    "endproperty",   "endsequence",  "enum",         "expect",
    "export",        "extends",      "extern",       "final",
    "first_match",   "foreach",      "forkjoin",     "iff",
    "ignore_bins",   "illegal_bins", "import",       "inside",
    "int",           "interface",    "intersect",    "join_any",
    "join_none",     "local",        "logic",        "longint",
    "matches",       "modport",      "new",          "null",
    "package",       "packed",       "priority",     "program",
    "property",      "protected",    "pure",         "rand",
    "randc",         "randcase",     "randsequence", "ref",
    "return",        "sequence",     "shortint",     "shortreal",
    "solve",         "static",       "string",       "struct",
    "super",         "tagged",       "this",         "throughout",
    "timeprecision", "timeunit",     "type",         "typedef",
    "union",         "unique",       "var",          "virtual",
    "void",          "wait_order",   "wildcard",     "with",
    "within",
};

// Table 22-5 -- what IEEE 1800-2009 reserves over the four lists it
// includes.
inline constexpr const char* kTable225Words[] = {
    "accept_on",      "checker",        "endchecker",   "eventually",
    "global",         "implies",        "let",          "nexttime",
    "reject_on",      "restrict",       "s_always",     "s_eventually",
    "s_nexttime",     "s_until",        "s_until_with", "strong",
    "sync_accept_on", "sync_reject_on", "unique0",      "until",
    "until_with",     "untyped",        "weak",
};

// Table 22-6 -- what IEEE 1800-2012 and later reserve over Table 22-5.
inline constexpr const char* kTable226Words[] = {"implements", "interconnect",
                                                 "nettype", "soft"};

// A reserved word paired with the token kind the lexer folds it to once the
// version reserving it is in force.
struct VersionedWord {
  const char* text;
  TokenKind kind;
};

// Table 22-2 -- what IEEE 1364-2001 reserves over Table 22-1. With the keyword
// each entry names.
inline constexpr VersionedWord kTable222[] = {
    {"automatic", TokenKind::kKwAutomatic},
    {"cell", TokenKind::kKwCell},
    {"config", TokenKind::kKwConfig},
    {"design", TokenKind::kKwDesign},
    {"endconfig", TokenKind::kKwEndconfig},
    {"endgenerate", TokenKind::kKwEndgenerate},
    {"generate", TokenKind::kKwGenerate},
    {"genvar", TokenKind::kKwGenvar},
    {"incdir", TokenKind::kKwIncdir},
    {"include", TokenKind::kKwInclude},
    {"instance", TokenKind::kKwInstance},
    {"liblist", TokenKind::kKwLiblist},
    {"library", TokenKind::kKwLibrary},
    {"localparam", TokenKind::kKwLocalparam},
    {"noshowcancelled", TokenKind::kKwNoshowcancelled},
    {"pulsestyle_ondetect", TokenKind::kKwPulsestyleOndetect},
    {"pulsestyle_onevent", TokenKind::kKwPulsestyleOnevent},
    {"showcancelled", TokenKind::kKwShowcancelled},
    {"signed", TokenKind::kKwSigned},
    {"unsigned", TokenKind::kKwUnsigned},
    {"use", TokenKind::kKwUse},
};

// Table 22-4 -- what IEEE 1364-2005 and SystemVerilog reserve over the
// Verilog tables above. With the keyword each entry names.
inline constexpr VersionedWord kTable224[] = {
    {"alias", TokenKind::kKwAlias},
    {"always_comb", TokenKind::kKwAlwaysComb},
    {"always_ff", TokenKind::kKwAlwaysFF},
    {"always_latch", TokenKind::kKwAlwaysLatch},
    {"assert", TokenKind::kKwAssert},
    {"assume", TokenKind::kKwAssume},
    {"before", TokenKind::kKwBefore},
    {"bind", TokenKind::kKwBind},
    {"bins", TokenKind::kKwBins},
    {"binsof", TokenKind::kKwBinsof},
    {"bit", TokenKind::kKwBit},
    {"break", TokenKind::kKwBreak},
    {"byte", TokenKind::kKwByte},
    {"chandle", TokenKind::kKwChandle},
    {"class", TokenKind::kKwClass},
    {"clocking", TokenKind::kKwClocking},
    {"const", TokenKind::kKwConst},
    {"constraint", TokenKind::kKwConstraint},
    {"context", TokenKind::kKwContext},
    {"continue", TokenKind::kKwContinue},
    {"cover", TokenKind::kKwCover},
    {"covergroup", TokenKind::kKwCovergroup},
    {"coverpoint", TokenKind::kKwCoverpoint},
    {"cross", TokenKind::kKwCross},
    {"dist", TokenKind::kKwDist},
    {"do", TokenKind::kKwDo},
    {"endclass", TokenKind::kKwEndclass},
    {"endclocking", TokenKind::kKwEndclocking},
    {"endgroup", TokenKind::kKwEndgroup},
    {"endinterface", TokenKind::kKwEndinterface},
    {"endpackage", TokenKind::kKwEndpackage},
    {"endprogram", TokenKind::kKwEndprogram},
    {"endproperty", TokenKind::kKwEndproperty},
    {"endsequence", TokenKind::kKwEndsequence},
    {"enum", TokenKind::kKwEnum},
    {"expect", TokenKind::kKwExpect},
    {"export", TokenKind::kKwExport},
    {"extends", TokenKind::kKwExtends},
    {"extern", TokenKind::kKwExtern},
    {"final", TokenKind::kKwFinal},
    {"first_match", TokenKind::kKwFirstMatch},
    {"foreach", TokenKind::kKwForeach},
    {"forkjoin", TokenKind::kKwForkjoin},
    {"iff", TokenKind::kKwIff},
    {"ignore_bins", TokenKind::kKwIgnoreBins},
    {"illegal_bins", TokenKind::kKwIllegalBins},
    {"import", TokenKind::kKwImport},
    {"inside", TokenKind::kKwInside},
    {"int", TokenKind::kKwInt},
    {"interface", TokenKind::kKwInterface},
    {"intersect", TokenKind::kKwIntersect},
    {"join_any", TokenKind::kKwJoinAny},
    {"join_none", TokenKind::kKwJoinNone},
    {"local", TokenKind::kKwLocal},
    {"logic", TokenKind::kKwLogic},
    {"longint", TokenKind::kKwLongint},
    {"matches", TokenKind::kKwMatches},
    {"modport", TokenKind::kKwModport},
    {"new", TokenKind::kKwNew},
    {"null", TokenKind::kKwNull},
    {"package", TokenKind::kKwPackage},
    {"packed", TokenKind::kKwPacked},
    {"priority", TokenKind::kKwPriority},
    {"program", TokenKind::kKwProgram},
    {"property", TokenKind::kKwProperty},
    {"protected", TokenKind::kKwProtected},
    {"pure", TokenKind::kKwPure},
    {"rand", TokenKind::kKwRand},
    {"randc", TokenKind::kKwRandc},
    {"randcase", TokenKind::kKwRandcase},
    {"randsequence", TokenKind::kKwRandsequence},
    {"ref", TokenKind::kKwRef},
    {"return", TokenKind::kKwReturn},
    {"sequence", TokenKind::kKwSequence},
    {"shortint", TokenKind::kKwShortint},
    {"shortreal", TokenKind::kKwShortreal},
    {"solve", TokenKind::kKwSolve},
    {"static", TokenKind::kKwStatic},
    {"string", TokenKind::kKwString},
    {"struct", TokenKind::kKwStruct},
    {"super", TokenKind::kKwSuper},
    {"tagged", TokenKind::kKwTagged},
    {"this", TokenKind::kKwThis},
    {"throughout", TokenKind::kKwThroughout},
    {"timeprecision", TokenKind::kKwTimeprecision},
    {"timeunit", TokenKind::kKwTimeunit},
    {"type", TokenKind::kKwType},
    {"typedef", TokenKind::kKwTypedef},
    {"union", TokenKind::kKwUnion},
    {"unique", TokenKind::kKwUnique},
    {"var", TokenKind::kKwVar},
    {"virtual", TokenKind::kKwVirtual},
    {"void", TokenKind::kKwVoid},
    {"wait_order", TokenKind::kKwWaitOrder},
    {"wildcard", TokenKind::kKwWildcard},
    {"with", TokenKind::kKwWith},
    {"within", TokenKind::kKwWithin},
};

// Table 22-5 -- what IEEE 1800-2009 reserves over the four lists it
// includes. With the keyword each entry names.
inline constexpr VersionedWord kTable225[] = {
    {"accept_on", TokenKind::kKwAcceptOn},
    {"checker", TokenKind::kKwChecker},
    {"endchecker", TokenKind::kKwEndchecker},
    {"eventually", TokenKind::kKwEventually},
    {"global", TokenKind::kKwGlobal},
    {"implies", TokenKind::kKwImplies},
    {"let", TokenKind::kKwLet},
    {"nexttime", TokenKind::kKwNexttime},
    {"reject_on", TokenKind::kKwRejectOn},
    {"restrict", TokenKind::kKwRestrict},
    {"s_always", TokenKind::kKwSAlways},
    {"s_eventually", TokenKind::kKwSEventually},
    {"s_nexttime", TokenKind::kKwSNexttime},
    {"s_until", TokenKind::kKwSUntil},
    {"s_until_with", TokenKind::kKwSUntilWith},
    {"strong", TokenKind::kKwStrong},
    {"sync_accept_on", TokenKind::kKwSyncAcceptOn},
    {"sync_reject_on", TokenKind::kKwSyncRejectOn},
    {"unique0", TokenKind::kKwUnique0},
    {"until", TokenKind::kKwUntil},
    {"until_with", TokenKind::kKwUntilWith},
    {"untyped", TokenKind::kKwUntyped},
    {"weak", TokenKind::kKwWeak},
};

// Table 22-6 -- what IEEE 1800-2012 and later reserve over Table 22-5. With the
// keyword each entry names.
inline constexpr VersionedWord kTable226[] = {
    {"implements", TokenKind::kKwImplements},
    {"interconnect", TokenKind::kKwInterconnect},
    {"nettype", TokenKind::kKwNettype},
    {"soft", TokenKind::kKwSoft},
};
