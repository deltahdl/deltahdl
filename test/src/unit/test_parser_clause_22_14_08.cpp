#include <cstddef>
#include <iterator>
#include <map>
#include <string>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// Table 22-1, the first of the five lists this version_specifier includes.
constexpr const char* kTable221[] = {
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

// Table 22-2, the second included list.
constexpr const char* kTable222[] = {"automatic",
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
                                     "use"};

// Table 22-3, the third included list, which holds one word.
constexpr const char* kTable223[] = {
    "uwire",
};

// Table 22-4, the fourth included list.
constexpr const char* kTable224[] = {
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

// Table 22-5, the fifth included list.
constexpr const char* kTable225[] = {
    "accept_on",      "checker",        "endchecker",   "eventually",
    "global",         "implies",        "let",          "nexttime",
    "reject_on",      "restrict",       "s_always",     "s_eventually",
    "s_nexttime",     "s_until",        "s_until_with", "strong",
    "sync_accept_on", "sync_reject_on", "unique0",      "until",
    "until_with",     "untyped",        "weak",
};

// Table 22-6: what this version adds on top of the five lists it includes.
constexpr const char* kTable226[] = {"implements", "interconnect", "nettype",
                                     "soft"};

// Opens a region for one version_specifier around `body`. "1800-2009" is the
// union of the five lists this version includes, so it is the leg every
// Table 22-6 claim is measured against: a word free there and reserved here was
// added by this version_specifier.
std::string In(const char* spec, const std::string& body) {
  return std::string("`begin_keywords \"") + spec + "\"\n" + body +
         "`end_keywords\n";
}

std::string VarDecl(const char* word) {
  return std::string("module m;\n  reg [7:0] ") + word + ";\nendmodule\n";
}

// The identifier positions a declaration's own slot does not reach, each
// reached by its own production. One table serves both sweeps below -- the
// included lists' and this version's additions -- since what changes between
// them is the word put in the slot, not the slot.
struct Position {
  const char* what;
  const char* tmpl;
};
constexpr Position kPositions[] = {
    {"design element", "module @;\nendmodule\n"},
    {"port",
     "module m (input wire @, output wire y);\n"
     "  assign y = @;\n"
     "endmodule\n"},
    {"instance",
     "module ch (input wire a, output wire y);\n"
     "  assign y = a;\n"
     "endmodule\n"
     "module top;\n"
     "  wire a, b;\n"
     "  ch @ (.a(a), .y(b));\n"
     "endmodule\n"},
    {"task",
     "module m;\n"
     "  reg [7:0] r;\n"
     "  task @; r = 8'd1; endtask\n"
     "  initial begin : blk @; end\n"
     "endmodule\n"},
    {"function",
     "module m;\n"
     "  reg [7:0] r;\n"
     "  function [7:0] @(input reg [7:0] n);\n"
     "    @ = n + n;\n"
     "  endfunction\n"
     "  initial r = @(8'd4);\n"
     "endmodule\n"},
    {"gate instance",
     "module m (input wire a, output wire y);\n"
     "  and @ (y, a, a);\n"
     "endmodule\n"},
    {"genvar",
     "module m;\n"
     "  genvar @;\n"
     "  generate\n"
     "    for (@ = 0; @ < 2; @ = @ + 1) begin : blk\n"
     "      reg [7:0] slot;\n"
     "    end\n"
     "  endgenerate\n"
     "endmodule\n"},
    {"named block",
     "module m;\n"
     "  reg [7:0] r;\n"
     "  initial begin : @ r = 8'd1; end\n"
     "endmodule\n"},
};

// Substitutes `word` for every placeholder in one position template.
std::string AtPosition(const Position& p, const char* word) {
  std::string src = p.tmpl;
  for (auto at = src.find('@'); at != std::string::npos;
       at = src.find('@', at + 1))
    src.replace(at, 1, word);
  return src;
}

// Two of Table 22-4's entries open an aggregate type declaration, and a
// declaration whose identifier slot holds one is read as the start of such a
// type; the parser does not terminate on that with no directive in force
// either, so the fault is not this subclause's. Both are swept in the
// identifier slot at the lexer and preprocessor stages instead.
bool IsAggregateOpenerWord(const std::string& word) {
  return word == "struct" || word == "union";
}

// What a constraint block recorded for the fourth added word. Shared by the two
// tests below so each reads as a tally rather than as a walk.
struct SoftTally {
  size_t blocks = 0;
  size_t relations = 0;
  size_t dists = 0;
  size_t refs = 0;
  size_t discarded = 0;
};

SoftTally TallySoft(const ParseResult& r, const char* expected_var) {
  SoftTally t;
  for (auto* member : r.cu->classes[0]->members) {
    if (member->kind != ClassMemberKind::kConstraint) continue;
    ++t.blocks;
    t.relations += member->constraint_soft_exprs.size();
    t.dists += member->constraint_soft_dist_refs.size();
    t.refs += member->constraint_soft_refs.size();
    t.discarded += member->constraint_disable_soft_refs.size();
    for (const auto& ref : member->constraint_soft_refs)
      EXPECT_EQ(ref.name, expected_var);
    for (const auto& ref : member->constraint_disable_soft_refs)
      EXPECT_EQ(ref.name, expected_var);
  }
  return t;
}

// The five included lists swept whole in an identifier slot, table by table.
// Each entry is rejected under this version, and -- for every list but the
// first, which has no earlier version to be measured against -- the very same
// declaration is accepted under the union of the lists that one is built on and
// read back off the tree, so the rejection is this version's list doing its
// work rather than an unrelated parse failure. The table name travels with
// every failure message. What the sweeps do not show is the keyword roles
// surviving, which the tests further down carry, one per included list.
TEST(CompilerDirectiveParsing, SystemVerilog2012ReservesEveryIncludedKeyword) {
  struct IncludedTable {
    const char* what;
    const char* const* words;
    size_t count;
    // Where the entry is still an ordinary identifier; null for the first list.
    const char* earlier;
    bool (*skip)(const std::string&);
    size_t expected_swept;
  };
  const IncludedTable kTables[] = {
      {"Table 22-1", kTable221, std::size(kTable221), nullptr, nullptr, 102},
      {"Table 22-2", kTable222, std::size(kTable222), "1364-1995", nullptr, 21},
      {"Table 22-3", kTable223, std::size(kTable223), "1364-2001", nullptr, 1},
      {"Table 22-4", kTable224, std::size(kTable224), "1364-2005",
       IsAggregateOpenerWord, 95},
      {"Table 22-5", kTable225, std::size(kTable225), "1800-2005", nullptr, 23},
  };
  EXPECT_EQ(std::size(kTable221), 102u);
  EXPECT_EQ(std::size(kTable222), 21u);
  EXPECT_EQ(std::size(kTable223), 1u);
  EXPECT_EQ(std::size(kTable224), 97u);
  EXPECT_EQ(std::size(kTable225), 23u);

  for (const auto& t : kTables) {
    size_t swept = 0;
    for (size_t i = 0; i < t.count; ++i) {
      const char* word = t.words[i];
      if (t.skip != nullptr && t.skip(word)) continue;
      ++swept;

      EXPECT_FALSE(ParseWithPreprocessorOk(In("1800-2012", VarDecl(word))))
          << word << " is included from " << t.what << " and stays reserved";
      if (t.earlier == nullptr) continue;

      auto freed = ParseWithPreprocessor(In(t.earlier, VarDecl(word)));
      ASSERT_NE(freed.cu, nullptr) << t.what << ' ' << word;
      EXPECT_FALSE(freed.has_errors) << t.what << ' ' << word;
      EXPECT_TRUE(HasItemKindNamed(freed.cu->modules[0]->items,
                                   ModuleItemKind::kVarDecl, word))
          << word << " is an addition of " << t.what;
    }
    EXPECT_EQ(swept, t.expected_swept) << t.what;
  }

  // Two lists were published for the same Verilog standard and they disagree on
  // exactly these ten words. Each is reserved here and names a variable under
  // the companion list that drops them, which is how this stage shows the full
  // list is what gets inherited.
  const char* kConfigurationWords[] = {
      "cell",    "config",   "design",  "endconfig", "incdir",
      "include", "instance", "liblist", "library",   "use",
  };
  for (const char* word : kConfigurationWords) {
    auto dropped =
        ParseWithPreprocessor(In("1364-2001-noconfig", VarDecl(word)));
    ASSERT_NE(dropped.cu, nullptr) << word;
    EXPECT_FALSE(dropped.has_errors) << word;
    EXPECT_TRUE(HasItemKindNamed(dropped.cu->modules[0]->items,
                                 ModuleItemKind::kVarDecl, word))
        << word << " names a variable under the configuration-free list";
  }
}

// Table 22-6 swept in an identifier slot, with the leg that makes each entry an
// addition. The word cannot name a variable here, and under "1800-2009" -- the
// union of everything this version includes -- the very same declaration is
// built and read back off the tree. Both legs together make the word this
// version_specifier's own rather than anything it inherits.
TEST(CompilerDirectiveParsing, SystemVerilog2012ReservesEveryWordItAdds) {
  EXPECT_EQ(std::size(kTable226), 4u);
  for (const char* word : kTable226) {
    EXPECT_FALSE(ParseWithPreprocessorOk(In("1800-2012", VarDecl(word))))
        << word << " is one of the words this version adds";

    auto freed = ParseWithPreprocessor(In("1800-2009", VarDecl(word)));
    ASSERT_NE(freed.cu, nullptr) << word;
    EXPECT_FALSE(freed.has_errors) << word;
    ASSERT_EQ(freed.cu->modules.size(), 1u) << word;
    EXPECT_TRUE(HasItemKindNamed(freed.cu->modules[0]->items,
                                 ModuleItemKind::kVarDecl, word))
        << word << " is free under everything this version includes";
  }
}

// Being on this version's list has to stop a word from naming anything at all,
// so one word from each of the five *included* tables is put in turn in every
// position above. Table 22-6 is absent here on purpose: its position axis is
// carried by the test below, which runs the same table against all four added
// words and asserts this rejection alongside its accepting counterpart.
TEST(CompilerDirectiveParsing,
     SystemVerilog2012ReservedWordsFillNoIdentifierPosition) {
  // One word from each of the five included tables.
  const char* kReserved[] = {"wire", "generate", "uwire", "logic", "until"};

  for (const auto& p : kPositions) {
    for (const char* word : kReserved) {
      EXPECT_FALSE(
          ParseWithPreprocessorOk(In("1800-2012", AtPosition(p, word))))
          << word << " cannot name a " << p.what << " under this version";
    }
  }
}

// The other side of the addition across those same positions. The sweep above
// closes the variable-declaration slot but does not show the added words free
// in any *other* position under the lists this version includes. So all four
// are put in every position under "1800-2009", where they are still ordinary
// identifiers, each paired with the same source under this version. None of
// the four opens a design element, so the region machinery stays out of the
// way.
TEST(CompilerDirectiveParsing,
     SystemVerilog2012AddedWordsNameEntitiesUnderIncludedLists) {
  for (const auto& p : kPositions) {
    for (const char* word : kTable226) {
      std::string src = AtPosition(p, word);
      EXPECT_TRUE(ParseWithPreprocessorOk(In("1800-2009", src)))
          << p.what << ": everything this version includes leaves " << word
          << " free";
      EXPECT_FALSE(ParseWithPreprocessorOk(In("1800-2012", src)))
          << p.what << ": this version reserves " << word;
    }
  }

  // Two of those positions read back, so the accepting legs are observed naming
  // things rather than merely parsing.
  auto named_module =
      ParseWithPreprocessor(In("1800-2009", "module soft;\nendmodule\n"));
  ASSERT_NE(named_module.cu, nullptr);
  ASSERT_EQ(named_module.cu->modules.size(), 1u);
  EXPECT_EQ(named_module.cu->modules[0]->name, "soft");

  auto named_gate =
      ParseWithPreprocessor(In("1800-2009",
                               "module m (input wire a, output wire y);\n"
                               "  and nettype (y, a, a);\n"
                               "endmodule\n"));
  ASSERT_NE(named_gate.cu, nullptr);
  auto* gate = FindGateByKind(named_gate.cu->modules[0]->items, GateKind::kAnd);
  ASSERT_NE(gate, nullptr);
  EXPECT_EQ(gate->gate_inst_name, "nettype");
}

// The first of the keyword roles this version's additions exist for: the clause
// by which a class declares the interface classes it honours. Two named in one
// clause land as two entries, kept apart from the single base inherited through
// the older `extends` of the fourth included list, whose `interface` and `pure
// virtual` the interface classes are themselves written with.
TEST(CompilerDirectiveParsing, SystemVerilog2012AddedImplementsOpensAClause) {
  const std::string kSrc =
      "interface class reader;\n"
      "  pure virtual function int read();\n"
      "endclass\n"
      "interface class writer;\n"
      "  pure virtual function void write(int v);\n"
      "endclass\n"
      "class base;\n"
      "  int held;\n"
      "endclass\n"
      "class port_t extends base implements reader, writer;\n"
      "  virtual function int read(); return held; endfunction\n"
      "  virtual function void write(int v); held = v; endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n";

  auto r = ParseWithPreprocessor(In("1800-2012", kSrc));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  const ClassDecl* impl = nullptr;
  for (auto* c : r.cu->classes) {
    if (c->name == "port_t") impl = c;
    if (c->name == "reader" || c->name == "writer")
      EXPECT_TRUE(c->is_interface);
  }
  ASSERT_NE(impl, nullptr);
  ASSERT_EQ(impl->implements_types.size(), 2u);
  EXPECT_EQ(impl->implements_types[0].name, "reader");
  EXPECT_EQ(impl->implements_types[1].name, "writer");
  // The clause this version adds is distinct from the inheritance clause the
  // fourth included list already offers.
  EXPECT_EQ(impl->base_class, "base");

  EXPECT_FALSE(ParseWithPreprocessorOk(In("1800-2009", kSrc)));
}

// The second added word, which opens a net whose type is left to be settled by
// what it connects. It is written in the two positions the production admits --
// a declaration inside a design element and a port in the header -- each
// landing with the mark that separates it from an ordinary net. The optional
// signedness and packed dimensions are exercised too, being parsed by the same
// branch.
TEST(CompilerDirectiveParsing,
     SystemVerilog2012AddedInterconnectOpensNetsAndPorts) {
  const std::string kSrc =
      "module m (interconnect [3:0] p, input wire a, output wire y);\n"
      "  interconnect          scalar_ic;\n"
      "  interconnect [7:0]    bus_ic;\n"
      "  interconnect signed [7:0] signed_ic;\n"
      "  wire         [7:0]    plain;\n"
      "  assign y = a;\n"
      "endmodule\n";

  auto r = ParseWithPreprocessor(In("1800-2012", kSrc));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto* m = r.cu->modules[0];
  ASSERT_EQ(m->ports.size(), 3u);
  EXPECT_TRUE(m->ports[0].data_type.is_interconnect);
  EXPECT_TRUE(m->ports[0].data_type.is_net);
  EXPECT_FALSE(m->ports[1].data_type.is_interconnect);

  size_t marked = 0;
  for (auto* item : m->items) {
    if (item->kind != ModuleItemKind::kNetDecl) continue;
    if (item->name == "plain") {
      EXPECT_FALSE(item->data_type.is_interconnect);
      continue;
    }
    EXPECT_TRUE(item->data_type.is_interconnect) << item->name;
    if (item->name == "signed_ic") EXPECT_TRUE(item->data_type.is_signed);
    if (item->name == "bus_ic") EXPECT_FALSE(item->data_type.is_signed);
    ++marked;
  }
  EXPECT_EQ(marked, 3u);

  EXPECT_FALSE(ParseWithPreprocessorOk(In("1800-2009", kSrc)));
}

// The direction and signedness qualifiers the interconnect form admits, which
// the test above does not reach: the word may stand behind each of the three
// directions a port header names, and the declaration takes the unsigned
// qualifier as well as the signed one. Every form is refused under the union of
// the lists this version includes.
TEST(CompilerDirectiveParsing,
     SystemVerilog2012AddedInterconnectTakesQualifiers) {
  const std::string kPorts =
      "module m (input interconnect [3:0] a, output interconnect [7:0] b,\n"
      "          inout interconnect c);\n"
      "endmodule\n";

  auto r = ParseWithPreprocessor(In("1800-2012", kPorts));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 3u);
  const Direction kDirections[] = {Direction::kInput, Direction::kOutput,
                                   Direction::kInout};
  for (size_t i = 0; i < ports.size(); ++i) {
    EXPECT_TRUE(ports[i].data_type.is_interconnect) << ports[i].name;
    EXPECT_EQ(ports[i].direction, kDirections[i]) << ports[i].name;
  }
  EXPECT_FALSE(ParseWithPreprocessorOk(In("1800-2009", kPorts)));

  // The declaration form's other signedness qualifier.
  const std::string kUnsigned =
      "module m;\n"
      "  interconnect unsigned [3:0] q;\n"
      "endmodule\n";
  auto u = ParseWithPreprocessor(In("1800-2012", kUnsigned));
  ASSERT_NE(u.cu, nullptr);
  EXPECT_FALSE(u.has_errors);
  for (auto* item : u.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kNetDecl) continue;
    EXPECT_TRUE(item->data_type.is_interconnect);
    EXPECT_FALSE(item->data_type.is_signed);
  }
  EXPECT_FALSE(ParseWithPreprocessorOk(In("1800-2009", kUnsigned)));
}

// The third added word, which opens a declaration binding a name to a net's
// data type. Both forms are here: the plain one and the one naming the function
// that resolves multiple drivers, each read back with the type it bound. The
// production's own negative -- the data type is not optional -- is here too,
// and it is a diagnostic only a keyword can raise.
TEST(CompilerDirectiveParsing, SystemVerilog2012AddedNettypeOpensDeclarations) {
  const std::string kSrc =
      "module m;\n"
      "  function automatic real resolve_sum(input real drivers[]);\n"
      "    return 0.0;\n"
      "  endfunction\n"
      "  nettype logic [7:0] byte_net;\n"
      "  nettype real        analog_net with resolve_sum;\n"
      "  byte_net   bn;\n"
      "endmodule\n";

  auto r = ParseWithPreprocessor(In("1800-2012", kSrc));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  size_t nettypes = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kNettypeDecl) continue;
    ++nettypes;
    if (item->name == "byte_net") {
      EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kLogic);
      EXPECT_TRUE(item->nettype_resolve_func.empty());
    }
    if (item->name == "analog_net") {
      EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kReal);
      EXPECT_EQ(item->nettype_resolve_func, "resolve_sum");
    }
  }
  EXPECT_EQ(nettypes, 2u);

  // The declaration's own negative: the data type is required.
  EXPECT_FALSE(ParseWithPreprocessorOk(
      In("1800-2012", "module m;\n  nettype lone;\nendmodule\n")));

  EXPECT_FALSE(ParseWithPreprocessorOk(In("1800-2009", kSrc)));
}

// The remaining forms of the declaration the third added word opens: the
// resolution function may be reached through a package scope rather than by a
// bare name, a branch of its own, and the declaration is a package item as well
// as a design-element item. Neither can be written under the included lists.
TEST(CompilerDirectiveParsing, SystemVerilog2012AddedNettypeTakesEveryForm) {
  const std::string kScoped =
      "package pkg;\n"
      "  function automatic real res(input real drivers[]);\n"
      "    return 0.0;\n"
      "  endfunction\n"
      "endpackage\n"
      "module m;\n"
      "  nettype real analog_net with pkg::res;\n"
      "endmodule\n";

  auto r = ParseWithPreprocessor(In("1800-2012", kScoped));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* scoped =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kNettypeDecl);
  ASSERT_NE(scoped, nullptr);
  EXPECT_EQ(scoped->name, "analog_net");
  // The trailing name is the resolver; the scope qualifying it is consumed by
  // the same branch.
  EXPECT_EQ(scoped->nettype_resolve_func, "res");
  EXPECT_FALSE(ParseWithPreprocessorOk(In("1800-2009", kScoped)));

  // The second position: a package item rather than a design-element item.
  const std::string kInPackage =
      "package pkg;\n"
      "  nettype logic [7:0] byte_net;\n"
      "endpackage\n"
      "module m;\n"
      "endmodule\n";
  auto pk = ParseWithPreprocessor(In("1800-2012", kInPackage));
  ASSERT_NE(pk.cu, nullptr);
  ASSERT_EQ(pk.cu->packages.size(), 1u);
  EXPECT_FALSE(pk.has_errors);
  EXPECT_TRUE(HasItemKindNamed(pk.cu->packages[0]->items,
                               ModuleItemKind::kNettypeDecl, "byte_net"));
  EXPECT_FALSE(ParseWithPreprocessorOk(In("1800-2009", kInPackage)));
}

// The fourth added word, the only one with two unrelated keyword roles, so both
// are here. As a union qualifier it marks a type whose members overlay one
// another without being packed; in a constraint block it marks a relation the
// solver may drop and discards the relations already placed on a variable. Its
// negative is the qualifier's own exclusivity rule: a union takes at most one
// of the two qualifiers it admits.
//
// The constraint half has no paired rejection under "1800-2009": a constraint
// body is scanned token by token rather than parsed as a grammar, so a stray
// identifier where the word stood is absorbed. What the pairing shows there is
// that nothing is *captured*. The union half does reject outright.
TEST(CompilerDirectiveParsing,
     SystemVerilog2012AddedSoftQualifiesUnionsAndConstraints) {
  const std::string kUnion =
      "module m;\n"
      "  typedef union soft { logic [7:0] a; logic [7:0] b; } overlay_t;\n"
      "  typedef union      { logic [7:0] c; logic [7:0] d; } plain_t;\n"
      "  overlay_t u;\n"
      "endmodule\n";

  auto r = ParseWithPreprocessor(In("1800-2012", kUnion));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  size_t typedefs = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kTypedef) continue;
    ++typedefs;
    if (item->name == "overlay_t") EXPECT_TRUE(item->typedef_type.is_soft);
    if (item->name == "plain_t") EXPECT_FALSE(item->typedef_type.is_soft);
  }
  EXPECT_EQ(typedefs, 2u);
  EXPECT_FALSE(ParseWithPreprocessorOk(In("1800-2009", kUnion)));

  // The qualifier's exclusivity rule, which only attaches when the word is read
  // as a qualifier at all.
  EXPECT_FALSE(ParseWithPreprocessorOk(
      In("1800-2012",
         "module m;\n"
         "  typedef union soft tagged { logic [7:0] a; } both_t;\n"
         "endmodule\n")));

  // Both constraint productions the word appears in: the qualifier that opens a
  // droppable relation, and the directive that discards the relations already
  // placed on a variable. They are written in separate blocks so each is
  // counted on its own.
  const std::string kConstraint =
      "class c;\n"
      "  rand int v;\n"
      "  rand int w;\n"
      "  constraint cc { soft v == 43; w > 0; }\n"
      "  constraint dd { disable soft v; v == 7; }\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n";

  auto cr = ParseWithPreprocessor(In("1800-2012", kConstraint));
  ASSERT_NE(cr.cu, nullptr);
  EXPECT_FALSE(cr.has_errors);
  ASSERT_EQ(cr.cu->classes.size(), 1u);
  auto here = TallySoft(cr, "v");
  EXPECT_EQ(here.blocks, 2u);
  // One qualified relation captured; the two hard ones beside it are not.
  EXPECT_EQ(here.relations, 1u);
  EXPECT_EQ(here.refs, 1u);
  EXPECT_EQ(here.discarded, 1u);

  auto included = ParseWithPreprocessor(In("1800-2009", kConstraint));
  ASSERT_NE(included.cu, nullptr);
  ASSERT_EQ(included.cu->classes.size(), 1u);
  auto there = TallySoft(included, "v");
  EXPECT_EQ(there.blocks, 2u);
  EXPECT_EQ(there.relations, 0u) << "an ordinary identifier qualifies nothing";
  EXPECT_EQ(there.refs, 0u);
  EXPECT_EQ(there.discarded, 0u) << "and discards nothing";
}

// The remaining positions the fourth added word may qualify: a union type
// written straight into a data declaration rather than through a typedef, and a
// distribution rather than a plain relation inside a constraint block, recorded
// on a list of its own. The declaration form is refused outright under the
// included lists; the constraint form instead records nothing there.
TEST(CompilerDirectiveParsing, SystemVerilog2012AddedSoftTakesEveryPosition) {
  const std::string kDirectUnion =
      "module m;\n"
      "  union soft { logic [7:0] a; logic [7:0] b; } u;\n"
      "endmodule\n";
  auto r = ParseWithPreprocessor(In("1800-2012", kDirectUnion));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* u_decl =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kVarDecl);
  ASSERT_NE(u_decl, nullptr);
  EXPECT_EQ(u_decl->name, "u");
  EXPECT_TRUE(u_decl->data_type.is_soft);
  EXPECT_FALSE(ParseWithPreprocessorOk(In("1800-2009", kDirectUnion)));

  const std::string kSoftDist =
      "class c;\n"
      "  rand int v;\n"
      "  constraint cc { soft v dist {1 := 1, 2 := 3}; }\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n";
  auto d = ParseWithPreprocessor(In("1800-2012", kSoftDist));
  ASSERT_NE(d.cu, nullptr);
  ASSERT_EQ(d.cu->classes.size(), 1u);
  EXPECT_FALSE(d.has_errors);
  auto here = TallySoft(d, "v");
  // The distribution is captured on a list of its own, not as a plain relation.
  EXPECT_EQ(here.dists, 1u);
  EXPECT_EQ(here.refs, 1u);
  EXPECT_EQ(here.relations, 0u);

  auto there =
      TallySoft(ParseWithPreprocessor(In("1800-2009", kSoftDist)), "v");
  EXPECT_EQ(there.dists, 0u)
      << "an ordinary identifier qualifies no distribution";
  EXPECT_EQ(there.refs, 0u);
}

// Tables 22-1 and 22-3 in their keyword roles: inclusion is not only about what
// a word may no longer name. The gate primitives build structure, the resolved
// net types and drive strengths are written out, and the procedural statements
// build control flow.
TEST(CompilerDirectiveParsing,
     SystemVerilog2012IncludedVerilog1995WordsStillWork) {
  auto r = ParseWithPreprocessor(
      In("1800-2012",
         "module m (input wire a, inout wire b, output uwire y);\n"
         "  wand w; uwire [3:0] resolved; trireg (small) cap;\n"
         "  supply0 gnd; integer i; real rl;\n"
         "  time t; event e; reg [1:0] sel;\n"
         "  and  g1 (y, a, b);\n"
         "  nmos g2 (w, a, b);\n"
         "  initial begin\n"
         "    for (i = 0; i < 2; i = i + 1) rl = rl + 1.0;\n"
         "    repeat (2) t = t + 1;\n"
         "    while (i > 0) i = i - 1;\n"
         "    casez (sel)\n"
         "      2'b1?: i = 1;\n"
         "      default: i = 0;\n"
         "    endcase\n"
         "    -> e;\n"
         "  end\n"
         "endmodule\n"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto& items = r.cu->modules[0]->items;
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kNetDecl, "w"));
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kVarDecl, "i"));

  // The lone entry of the third included list, whose keyword role is a net type
  // of its own -- in a declaration and in a port, both still opening here.
  EXPECT_EQ(r.cu->modules[0]->ports.back().data_type.kind,
            DataTypeKind::kUwire);
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kNetDecl && item->name == "resolved")
      EXPECT_EQ(item->data_type.kind, DataTypeKind::kUwire);
  }

  auto* gate = FindGateByKind(items, GateKind::kAnd);
  ASSERT_NE(gate, nullptr);
  EXPECT_EQ(gate->gate_inst_name, "g1");
  EXPECT_NE(FindGateByKind(items, GateKind::kNmos), nullptr);
}

// Table 22-2 in its keyword role: a constant declaration, a loop generate
// construct, a subroutine qualifier, the signedness qualifiers, and the four
// pulse-control specify items. Its other half is the ten words a configuration
// is written with, which separates this list from its configuration-free
// companion: seven appear below and the declaration is built, while under that
// companion the very same source cannot be written.
TEST(CompilerDirectiveParsing,
     SystemVerilog2012IncludedVerilog2001WordsStillWork) {
  auto r = ParseWithPreprocessor(
      In("1800-2012",
         "module m (input wire a, output wire y);\n"
         "  localparam L = 2;\n"
         "  genvar g;\n"
         "  reg signed   [7:0] s;\n"
         "  reg unsigned [7:0] u;\n"
         "  generate\n"
         "    for (g = 0; g < L; g = g + 1) begin : blk\n"
         "      reg [7:0] slot;\n"
         "    end\n"
         "  endgenerate\n"
         "  function automatic [7:0] twice(input reg [7:0] n);\n"
         "    twice = n + n;\n"
         "  endfunction\n"
         "  assign y = a;\n"
         "  specify\n"
         "    pulsestyle_ondetect y;\n"
         "    pulsestyle_onevent y;\n"
         "    showcancelled y;\n"
         "    noshowcancelled y;\n"
         "    (a => y) = 1;\n"
         "  endspecify\n"
         "endmodule\n"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto& items = r.cu->modules[0]->items;
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kParamDecl, "L"));
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kFunctionDecl, "twice"));
  EXPECT_NE(FindItemByKind(items, ModuleItemKind::kGenerateFor), nullptr);
  EXPECT_NE(FindSpecifyBlock(items), nullptr);

  for (auto* item : items) {
    if (item->kind != ModuleItemKind::kVarDecl) continue;
    if (item->name == "s") EXPECT_TRUE(item->data_type.is_signed);
    if (item->name == "u") EXPECT_FALSE(item->data_type.is_signed);
  }

  const std::string kConfig =
      "module top;\nendmodule\n"
      "config config_a;\n"
      "  design top;\n"
      "  default liblist blue green;\n"
      "  instance top.u1 liblist red;\n"
      "  cell m1 use lib.m2;\n"
      "endconfig\n";
  auto cfg_r = ParseWithPreprocessor(In("1800-2012", kConfig));
  ASSERT_NE(cfg_r.cu, nullptr);
  EXPECT_FALSE(cfg_r.has_errors);
  ASSERT_EQ(cfg_r.cu->configs.size(), 1u);
  EXPECT_EQ(cfg_r.cu->configs[0]->name, "config_a");
  // One rule per clause below the design statement: the default liblist, the
  // instance rule, and the cell rule.
  EXPECT_EQ(cfg_r.cu->configs[0]->rules.size(), 3u);
  EXPECT_FALSE(ParseWithPreprocessorOk(In("1364-2001-noconfig", kConfig)));
  // The module alongside it parses under both, so that rejection belongs to the
  // configuration rather than to the source as a whole.
  EXPECT_TRUE(ParseWithPreprocessorOk(
      In("1364-2001-noconfig", "module top;\nendmodule\n")));
}

// The fourth included list in its keyword role, the largest thing this version
// inherits: data types, user-defined types, inferred processes, design
// elements, and the verification vocabulary the added words sit alongside.
TEST(CompilerDirectiveParsing,
     SystemVerilog2012IncludedSystemVerilog2005WordsStillWork) {
  const std::string kSrc =
      "package pkg;\n  localparam int WIDTH = 8;\nendpackage\n"
      "interface ifc;\n"
      "  logic [7:0] data;\n"
      "  modport source (output data);\n"
      "endinterface\n"
      "class base;\n"
      "  int v;\n"
      "  function new(); v = 1; endfunction\n"
      "endclass\n"
      "module m (input logic clk, input logic d, output logic q);\n"
      "  import pkg::*;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  typedef enum logic [1:0] {IDLE, BUSY} state_t;\n"
      "  typedef struct packed { logic [3:0] hi; logic [3:0] lo; } pair_t;\n"
      "  byte_t wide; state_t phase; pair_t split;\n"
      "  bit [7:0] as_bit; byte as_byte; shortint as_shortint;\n"
      "  int as_int; longint as_longint; string as_string;\n"
      "  chandle as_chandle; logic combo;\n"
      "  always_comb  combo = d;\n"
      "  always_ff  @(posedge clk) q <= combo;\n"
      "  always_latch if (clk) wide = {7'd0, d};\n"
      "  final begin end\n"
      "  property p_handshake; @(posedge clk) d; endproperty\n"
      "  sequence s_pulse; @(posedge clk) d; endsequence\n"
      "  initial begin\n"
      "    assert (as_int == 0);\n"
      "    foreach (as_string[j]) as_byte = 8'd0;\n"
      "    unique case (phase) IDLE: as_int = 1; default: as_int = 0; endcase\n"
      "  end\n"
      "endmodule\n";

  auto r = ParseWithPreprocessor(In("1800-2012", kSrc));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->name, "ifc");
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "base");

  auto& items = r.cu->modules[0]->items;
  for (const char* name : {"byte_t", "state_t", "pair_t"})
    EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kTypedef, name))
        << name;
  for (auto kind :
       {ModuleItemKind::kAlwaysCombBlock, ModuleItemKind::kAlwaysFFBlock,
        ModuleItemKind::kAlwaysLatchBlock, ModuleItemKind::kFinalBlock})
    EXPECT_NE(FindItemByKind(items, kind), nullptr);
  EXPECT_TRUE(
      HasItemKindNamed(items, ModuleItemKind::kPropertyDecl, "p_handshake"));
  EXPECT_TRUE(
      HasItemKindNamed(items, ModuleItemKind::kSequenceDecl, "s_pulse"));

  // Each two-state and opaque type this list adds opens its own declaration.
  const std::map<std::string_view, DataTypeKind> kDecls = {
      {"as_bit", DataTypeKind::kBit},
      {"as_byte", DataTypeKind::kByte},
      {"as_shortint", DataTypeKind::kShortint},
      {"as_int", DataTypeKind::kInt},
      {"as_longint", DataTypeKind::kLongint},
      {"as_string", DataTypeKind::kString},
      {"as_chandle", DataTypeKind::kChandle}};
  size_t typed_seen = 0;
  for (auto* item : items) {
    auto it = kDecls.find(item->name);
    if (item->kind != ModuleItemKind::kVarDecl || it == kDecls.end()) continue;
    EXPECT_EQ(item->data_type.kind, it->second) << item->name;
    ++typed_seen;
  }
  EXPECT_EQ(typed_seen, kDecls.size());

  EXPECT_FALSE(ParseWithPreprocessorOk(In("1364-2005", kSrc)));
}

// The fifth included list in its keyword role: a design element of its own, a
// declaration, an untyped formal, a case qualifier that permits no match, a
// restriction item, the single clocking block a design may mark, and the
// temporal operators a property expression is built from. None of it can be
// written under "1800-2005", the union of the lists that one is built on.
TEST(CompilerDirectiveParsing,
     SystemVerilog2012IncludedSystemVerilog2009WordsStillWork) {
  const std::string kSrc =
      "checker handshake (logic clk, logic req);\n"
      "  assert property (@(posedge clk) req);\n"
      "endchecker\n"
      "let gain = 21;\n"
      "module m (input logic clk, input logic req, input logic a,\n"
      "          input logic b);\n"
      "  logic [1:0] sel; logic [7:0] r;\n"
      "  let sum(untyped x, int y) = x + y;\n"
      "  global clocking gcb @(posedge clk); endclocking\n"
      "  restrict property (@(posedge clk) req);\n"
      "  handshake u_chk (clk, req);\n"
      "  property p; @(posedge clk) s_eventually a until_with b; endproperty\n"
      "  assert property (p);\n"
      "  initial begin\n"
      "    unique0 case (sel) 2'b01: r = 8'd1; default: r = 8'd0; endcase\n"
      "    unique0 if (req) r = 8'd3; else r = 8'd4;\n"
      "  end\n"
      "endmodule\n";

  auto r = ParseWithPreprocessor(In("1800-2012", kSrc));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->name, "handshake");
  EXPECT_TRUE(
      HasItemKindNamed(r.cu->cu_items, ModuleItemKind::kLetDecl, "gain"));

  auto& items = r.cu->modules[0]->items;
  auto* sum = FindItemByKind(items, ModuleItemKind::kLetDecl);
  ASSERT_NE(sum, nullptr);
  EXPECT_EQ(sum->name, "sum");
  ASSERT_EQ(sum->func_args.size(), 2u);
  EXPECT_EQ(sum->func_args[0].data_type.kind, DataTypeKind::kImplicit);
  EXPECT_EQ(sum->func_args[1].data_type.kind, DataTypeKind::kInt);
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kPropertyDecl, "p"));

  EXPECT_NE(FindItemByKind(items, ModuleItemKind::kRestrictProperty), nullptr);
  auto* clocking = FindItemByKind(items, ModuleItemKind::kClockingBlock);
  ASSERT_NE(clocking, nullptr);
  EXPECT_TRUE(clocking->is_global_clocking);

  auto* init = FindItemByKind(items, ModuleItemKind::kInitialBlock);
  ASSERT_NE(init, nullptr);
  ASSERT_NE(init->body, nullptr);
  size_t qualified = 0;
  for (auto* st : init->body->stmts) {
    if (st == nullptr) continue;
    if (st->kind != StmtKind::kCase && st->kind != StmtKind::kIf) continue;
    EXPECT_EQ(st->qualifier, CaseQualifier::kUnique0);
    ++qualified;
  }
  EXPECT_EQ(qualified, 2u);

  EXPECT_FALSE(ParseWithPreprocessorOk(In("1800-2005", kSrc)));
}

// The negative the six tables imply: a word none of them lists is an ordinary
// identifier under this version, so it names things freely and opens nothing.
// Both halves are here -- the same word naming a declaration and failing to be
// a data type -- because either alone would leave the other unchecked. This
// version is the last that reserves anything new, so what is bounded is the
// table's own membership: each word is a near miss of a real entry.
TEST(CompilerDirectiveParsing,
     SystemVerilog2012LeavesWordsOutsideTheTablesAsIdentifiers) {
  const char* kNotWords[] = {
      "implement", "implements_", "interconnects", "nettypes",
      "net_type",  "softly",      "soft_",
  };
  for (const char* word : kNotWords) {
    auto r = ParseWithPreprocessor(In("1800-2012", VarDecl(word)));
    ASSERT_NE(r.cu, nullptr) << word;
    EXPECT_FALSE(r.has_errors) << word;
    ASSERT_EQ(r.cu->modules.size(), 1u) << word;
    EXPECT_TRUE(HasItemKindNamed(r.cu->modules[0]->items,
                                 ModuleItemKind::kVarDecl, word))
        << word;

    std::string as_type =
        std::string("module m;\n  ") + word + " [7:0] v;\nendmodule\n";
    EXPECT_FALSE(ParseWithPreprocessorOk(In("1800-2012", as_type)))
        << word << " is not a data type under this version";
  }
}

}  // namespace
