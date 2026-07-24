#include <cstddef>
#include <iterator>
#include <string>

#include "fixture_elaborator.h"

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

// Table 22-2, the second included list -- included whole.
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

// The ten of Table 22-2 the configuration-free companion list drops -- what
// separates the two lists published for the same standard.
constexpr const char* kConfigurationWords[] = {
    "cell",    "config",   "design",  "endconfig", "incdir",
    "include", "instance", "liblist", "library",   "use",
};

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

const RtlirModule* FindModule(RtlirDesign* design, std::string_view name) {
  auto it = design->all_modules.find(name);
  return it == design->all_modules.end() ? nullptr : it->second;
}

const RtlirVariable* FindVar(RtlirDesign* design, std::string_view mod,
                             std::string_view name) {
  const auto* m = FindModule(design, mod);
  if (m == nullptr) return nullptr;
  for (const auto& var : m->variables) {
    if (var.name == name) return &var;
  }
  return nullptr;
}

const RtlirNet* FindNet(RtlirDesign* design, std::string_view mod,
                        std::string_view name) {
  const auto* m = FindModule(design, mod);
  if (m == nullptr) return nullptr;
  for (const auto& net : m->nets) {
    if (net.name == name) return &net;
  }
  return nullptr;
}

const RtlirParamDecl* FindParam(RtlirDesign* design, std::string_view mod,
                                std::string_view name) {
  const auto* m = FindModule(design, mod);
  if (m == nullptr) return nullptr;
  for (const auto& p : m->params) {
    if (p.name == name) return &p;
  }
  return nullptr;
}

bool HasProcess(RtlirDesign* design, std::string_view mod,
                RtlirProcessKind kind) {
  const auto* m = FindModule(design, mod);
  if (m == nullptr) return false;
  for (const auto& p : m->processes) {
    if (p.kind == kind) return true;
  }
  return false;
}

// How many elaborated variables in `mod` end in `suffix`, used to observe a
// loop generate construct without depending on per-iteration name spelling.
size_t CountVarsEndingIn(RtlirDesign* design, std::string_view mod,
                         std::string_view suffix) {
  size_t n = 0;
  const auto* m = FindModule(design, mod);
  if (m == nullptr) return n;
  for (const auto& var : m->variables) {
    if (var.name.size() >= suffix.size() &&
        var.name.substr(var.name.size() - suffix.size()) == suffix) {
      ++n;
    }
  }
  return n;
}

// Six of Table 22-1's entries name a gate primitive whose keyword may open a
// gate instantiation with no leading type, so a declaration whose identifier
// slot holds one is read as a malformed instantiation and elaborating it
// crashes -- with no directive in force either, so the fault is not this
// subclause's. These six are swept in the identifier slot at the parser stage
// instead, where the same source is rejected without incident.
bool IsGatePrimitiveWord(const std::string& word) {
  return word == "and" || word == "nand" || word == "nor" || word == "or" ||
         word == "xnor" || word == "xor";
}

// Two of Table 22-4's entries open an aggregate type declaration; a declaration
// whose identifier slot holds one is read as the start of such a type and the
// parser does not terminate on it, with no directive in force either, so the
// elaborator is never reached. Swept at the lexer and preprocessor instead.
bool IsAggregateOpenerWord(const std::string& word) {
  return word == "struct" || word == "union";
}

// The five included lists swept whole in an identifier slot, table by table.
// Each entry is reserved under this version, and -- for every list but the
// first, which has no earlier version to be measured against -- the same
// declaration elaborates into a variable of the width it asked for under the
// union of the lists that one is built on. The five sweeps share one test
// because they share one shape; the table name travels with every failure
// message. What they do not show is the keyword roles surviving, which the
// tests further down carry, one per included list.
TEST(SystemVerilog2012KeywordElaboration, IncludedWordsAreReservedAtThisStage) {
  struct IncludedTable {
    const char* what;
    const char* const* words;
    size_t count;
    // Where the entry is still an ordinary identifier; null for the first list.
    const char* earlier;
    // Entries the elaborator cannot be driven with, and why, above.
    bool (*skip)(const std::string&);
    size_t expected_swept;
  };
  const IncludedTable kTables[] = {
      {"Table 22-1", kTable221, std::size(kTable221), nullptr,
       IsGatePrimitiveWord, 96},
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

      ElabFixture reserved;
      ElaborateWithPreprocessor(In("1800-2012", VarDecl(word)), reserved, "m");
      EXPECT_TRUE(reserved.has_errors)
          << word << " is included from " << t.what << " and stays reserved";
      if (t.earlier == nullptr) continue;

      ElabFixture freed;
      auto* design =
          ElaborateWithPreprocessor(In(t.earlier, VarDecl(word)), freed, "m");
      ASSERT_NE(design, nullptr) << t.what << ' ' << word;
      EXPECT_FALSE(freed.has_errors) << t.what << ' ' << word;
      const auto* v = FindVar(design, "m", word);
      ASSERT_NE(v, nullptr) << t.what << ' ' << word;
      EXPECT_EQ(v->width, 8u) << t.what << ' ' << word;
    }
    EXPECT_EQ(swept, t.expected_swept) << t.what;
  }

  // Two lists were published for the same Verilog standard and they disagree on
  // exactly these ten words. Each is reserved here and names a variable under
  // the companion list that drops them, which is how this stage shows the full
  // list is what gets inherited.
  EXPECT_EQ(std::size(kConfigurationWords), 10u);
  for (const char* word : kConfigurationWords) {
    ElabFixture dropped;
    auto* design = ElaborateWithPreprocessor(
        In("1364-2001-noconfig", VarDecl(word)), dropped, "m");
    ASSERT_NE(design, nullptr) << word;
    EXPECT_FALSE(dropped.has_errors) << word;
    const auto* v = FindVar(design, "m", word);
    ASSERT_NE(v, nullptr) << word;
    EXPECT_EQ(v->width, 8u) << word;
  }
}

// Table 22-6 swept at this stage, with the leg that makes each entry an
// addition. The word cannot name an elaborated variable here, and under
// "1800-2009" -- the union of everything this version includes -- the same
// declaration reaches the design as a variable of the width it asked for.
// Reading it back keeps the accepting leg from being any elaboration that
// happens to succeed.
TEST(SystemVerilog2012KeywordElaboration, AddedWordsCannotNameVariables) {
  EXPECT_EQ(std::size(kTable226), 4u);
  for (const char* word : kTable226) {
    ElabFixture reserved;
    ElaborateWithPreprocessor(In("1800-2012", VarDecl(word)), reserved, "m");
    EXPECT_TRUE(reserved.has_errors) << word;

    ElabFixture freed;
    auto* design =
        ElaborateWithPreprocessor(In("1800-2009", VarDecl(word)), freed, "m");
    ASSERT_NE(design, nullptr) << word;
    EXPECT_FALSE(freed.has_errors) << word;
    const auto* v = FindVar(design, "m", word);
    ASSERT_NE(v, nullptr) << word;
    EXPECT_EQ(v->width, 8u) << word;
  }
}

// The added word whose construct becomes elaborated structure of its own kind.
// An interconnect net carries a net type no other word produces -- scalar and
// vector, in a port as well as in a declaration -- while the ordinary net
// beside it does not. Two elaborator rules turn on that mark: the generic
// connection carries no signedness, and it is not a net a declaration may drive
// from its own initializer. Each is shown against the ordinary net allowed
// exactly what it is refused.
TEST(SystemVerilog2012KeywordElaboration, AddedInterconnectNetsReachTheDesign) {
  const std::string kSrc =
      "module m (interconnect [3:0] p, inout interconnect [7:0] q,\n"
      "          input interconnect [1:0] r, output interconnect s,\n"
      "          input wire a, output wire y);\n"
      "  interconnect       scalar_ic;\n"
      "  interconnect [7:0] bus_ic;\n"
      "  wire         [7:0] plain;\n"
      "  assign y = a;\n"
      "endmodule\n";

  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(In("1800-2012", kSrc), f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* n = FindNet(design, "m", "scalar_ic");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->net_type, NetType::kInterconnect);
  EXPECT_EQ(n->width, 1u);
  n = FindNet(design, "m", "bus_ic");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->net_type, NetType::kInterconnect);
  EXPECT_EQ(n->width, 8u);
  n = FindNet(design, "m", "plain");
  ASSERT_NE(n, nullptr);
  EXPECT_NE(n->net_type, NetType::kInterconnect);

  const auto* m = FindModule(design, "m");
  ASSERT_NE(m, nullptr);
  // The mark survives every direction a port header may name, and the width
  // still comes from the packed range written beside the word. A generic
  // connection with no direction named is bidirectional, which is what the
  // first row records.
  ASSERT_EQ(m->ports.size(), 6u);
  struct PortCase {
    size_t index;
    Direction direction;
    uint32_t width;
  };
  const PortCase kMarked[] = {{0, Direction::kInout, 4},
                              {1, Direction::kInout, 8},
                              {2, Direction::kInput, 2},
                              {3, Direction::kOutput, 1}};
  for (const auto& c : kMarked) {
    EXPECT_TRUE(m->ports[c.index].is_interconnect) << c.index;
    EXPECT_EQ(m->ports[c.index].direction, c.direction) << c.index;
    EXPECT_EQ(m->ports[c.index].width, c.width) << c.index;
  }
  EXPECT_FALSE(m->ports[4].is_interconnect);

  // The first rule keyed off the mark: the generic connection has no
  // signedness, while an ordinary port may be declared signed.
  ElabFixture signed_ic;
  ElaborateWithPreprocessor(
      In("1800-2012", "module m (interconnect signed [3:0] p);\nendmodule\n"),
      signed_ic, "m");
  EXPECT_TRUE(signed_ic.has_errors);
  ElabFixture signed_wire;
  ElaborateWithPreprocessor(
      In("1800-2012", "module m (input wire signed [3:0] p);\nendmodule\n"),
      signed_wire, "m");
  EXPECT_FALSE(signed_wire.has_errors);

  // The second: an interconnect net takes no declaration assignment, while an
  // ordinary net does.
  ElabFixture ic_assign;
  ElaborateWithPreprocessor(
      In("1800-2012", "module m;\n  interconnect [3:0] q = 4'd1;\nendmodule\n"),
      ic_assign, "m");
  EXPECT_TRUE(ic_assign.has_errors);
  ElabFixture wire_assign;
  ElaborateWithPreprocessor(
      In("1800-2012", "module m;\n  wire [3:0] q = 4'd1;\nendmodule\n"),
      wire_assign, "m");
  EXPECT_FALSE(wire_assign.has_errors);

  ElabFixture included;
  ElaborateWithPreprocessor(In("1800-2009", kSrc), included, "m");
  EXPECT_TRUE(included.has_errors);
}

// The added word that binds a name to a net's data type. What the elaborator
// settles is the width every net declared with that name gets, so the nets are
// read back rather than the declaration. Both forms of the declaration are here
// and so is its own elaborator rule -- not every data type may stand in it --
// which is a diagnostic only a keyword can raise.
TEST(SystemVerilog2012KeywordElaboration,
     AddedNettypeDeclarationsResolveNetWidths) {
  const std::string kSrc =
      "module m;\n"
      "  function automatic real resolve_sum(input real drivers[]);\n"
      "    return 0.0;\n"
      "  endfunction\n"
      "  nettype logic [7:0] byte_net;\n"
      "  nettype byte_net    alias_net;\n"
      "  nettype real        analog_net with resolve_sum;\n"
      "  byte_net  wide;\n"
      "  alias_net through;\n"
      "  analog_net resolved;\n"
      "  wire      plain;\n"
      "endmodule\n";

  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(In("1800-2012", kSrc), f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* n = FindNet(design, "m", "wide");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->width, 8u);
  n = FindNet(design, "m", "through");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->width, 8u) << "the second name resolves through the first";
  // The second form of the declaration, which also names the function resolving
  // multiple drivers; the width still comes from the type the name was bound
  // to.
  n = FindNet(design, "m", "resolved");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->width, 64u);
  n = FindNet(design, "m", "plain");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->width, 1u);

  // A nettype whose data type is not one a net may carry.
  ElabFixture bad_type;
  ElaborateWithPreprocessor(
      In("1800-2012", "module m;\n  nettype string text_net;\nendmodule\n"),
      bad_type, "m");
  EXPECT_TRUE(bad_type.has_errors);

  ElabFixture included;
  ElaborateWithPreprocessor(In("1800-2009", kSrc), included, "m");
  EXPECT_TRUE(included.has_errors);
}

// The added word whose clause the elaborator itself acts on. Naming an
// interface class puts the implementing class under an obligation the
// elaborator checks: a class supplying every prototype elaborates clean, and
// the same class with one method removed is rejected. Both are shown, since the
// accepting leg alone would be consistent with the clause being ignored.
TEST(SystemVerilog2012KeywordElaboration,
     AddedImplementsClauseCarriesObligations) {
  const std::string kSrc =
      "interface class reader;\n"
      "  pure virtual function int read();\n"
      "endclass\n"
      "interface class writer;\n"
      "  pure virtual function void write(int v);\n"
      "endclass\n"
      "class port_t implements reader, writer;\n"
      "  int held;\n"
      "  virtual function int read(); return held; endfunction\n"
      "  virtual function void write(int v); held = v; endfunction\n"
      "endclass\n"
      "module m;\n"
      "  int result;\n"
      "  initial result = 0;\n"
      "endmodule\n";

  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(In("1800-2012", kSrc), f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  // The obligation from the first interface, unmet.
  ElabFixture missing_read;
  ElaborateWithPreprocessor(In("1800-2012",
                               "interface class reader;\n"
                               "  pure virtual function int read();\n"
                               "endclass\n"
                               "class port_t implements reader;\n"
                               "  int held;\n"
                               "endclass\n"
                               "module m;\n"
                               "  int result;\n"
                               "  initial result = 0;\n"
                               "endmodule\n"),
                            missing_read, "m");
  EXPECT_TRUE(missing_read.has_errors);

  // The same class without the clause is not under the obligation at all, so
  // what the rejection above tracks is the clause rather than the missing
  // method.
  ElabFixture no_clause;
  ElaborateWithPreprocessor(In("1800-2012",
                               "interface class reader;\n"
                               "  pure virtual function int read();\n"
                               "endclass\n"
                               "class port_t;\n"
                               "  int held;\n"
                               "endclass\n"
                               "module m;\n"
                               "  int result;\n"
                               "  initial result = 0;\n"
                               "endmodule\n"),
                            no_clause, "m");
  EXPECT_FALSE(no_clause.has_errors);

  ElabFixture included;
  ElaborateWithPreprocessor(In("1800-2009", kSrc), included, "m");
  EXPECT_TRUE(included.has_errors);
}

// The added word with two keyword roles, both reaching this stage. As a union
// qualifier it selects a type whose members share storage, shown in the width
// the variable ends up with: one member's worth rather than the sum. As a
// constraint qualifier it marks a relation the solver may drop, and the
// elaborator applies the rule that such a relation may only be placed on a
// variable randomized without a cycle -- with nothing to attach to when the
// word is an ordinary identifier, as the "1800-2009" leg shows.
TEST(SystemVerilog2012KeywordElaboration, AddedSoftQualifierReachesTheDesign) {
  const std::string kUnion =
      "module m;\n"
      "  typedef union soft { logic [7:0] a; logic [7:0] b; } overlay_t;\n"
      "  overlay_t u;\n"
      "  logic [7:0] plain;\n"
      "endmodule\n";

  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(In("1800-2012", kUnion), f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* u = FindVar(design, "m", "u");
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(u->width, 8u) << "the members share their storage";

  ElabFixture union_included;
  ElaborateWithPreprocessor(In("1800-2009", kUnion), union_included, "m");
  EXPECT_TRUE(union_included.has_errors);

  // The constraint role, and the rule the elaborator applies to it.
  const std::string kCyclic =
      "class c;\n"
      "  randc bit [3:0] v;\n"
      "  constraint cc { soft v == 4'd3; }\n"
      "endclass\n"
      "module m;\n"
      "  int result;\n"
      "  initial result = 0;\n"
      "endmodule\n";
  ElabFixture cyclic;
  ElaborateWithPreprocessor(In("1800-2012", kCyclic), cyclic, "m");
  EXPECT_TRUE(cyclic.has_errors);

  // The same relation on an ordinary random variable is accepted, so the
  // rejection above is the rule and not the qualifier being unusable.
  ElabFixture plain_rand;
  ElaborateWithPreprocessor(In("1800-2012",
                               "class c;\n"
                               "  rand bit [3:0] v;\n"
                               "  constraint cc { soft v == 4'd3; }\n"
                               "endclass\n"
                               "module m;\n"
                               "  int result;\n"
                               "  initial result = 0;\n"
                               "endmodule\n"),
                            plain_rand, "m");
  EXPECT_FALSE(plain_rand.has_errors);

  // Under everything this version includes the word qualifies nothing, so the
  // rule never attaches and the very same source elaborates clean.
  ElabFixture constraint_included;
  ElaborateWithPreprocessor(In("1800-2009", kCyclic), constraint_included, "m");
  EXPECT_FALSE(constraint_included.has_errors);
}

// Tables 22-1 and 22-3 doing their work, read back as elaborated structure. The
// net types are the sharpest part: each resolved and driven type has to survive
// into the design as itself rather than collapsing onto a plain wire.
TEST(SystemVerilog2012KeywordElaboration,
     IncludedVerilog1995WordsStillBuildDesign) {
  ElabFixture f;
  auto* design =
      ElaborateWithPreprocessor(In("1800-2012",
                                   "module m (input wire a, output wire y);\n"
                                   "  wand     wa;\n"
                                   "  wor      wo;\n"
                                   "  triand   ta;\n"
                                   "  trior    to;\n"
                                   "  tri0     t0;\n"
                                   "  tri1     t1;\n"
                                   "  trireg   tr;\n"
                                   "  supply0  gnd;\n"
                                   "  supply1  vdd;\n"
                                   "  uwire    uw;\n"
                                   "  uwire [7:0] uwv;\n"
                                   "  reg [7:0] r;\n"
                                   "  integer   i;\n"
                                   "  real      rl;\n"
                                   "  time      tm;\n"
                                   "  event     ev;\n"
                                   "  parameter P = 8;\n"
                                   "  and g1 (y, a, a);\n"
                                   "endmodule\n"),
                                f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  struct NetCase {
    const char* name;
    NetType type;
  };
  const NetCase kNets[] = {
      {"wa", NetType::kWand},
      {"wo", NetType::kWor},
      {"ta", NetType::kTriand},
      {"to", NetType::kTrior},
      {"t0", NetType::kTri0},
      {"t1", NetType::kTri1},
      {"tr", NetType::kTrireg},
      {"gnd", NetType::kSupply0},
      {"vdd", NetType::kSupply1},
      // The lone entry of the third included list, whose keyword role is a net
      // type of its own: reserved here, and still resolving to itself.
      {"uw", NetType::kUwire},
      {"uwv", NetType::kUwire},
  };
  for (const auto& c : kNets) {
    const auto* n = FindNet(design, "m", c.name);
    ASSERT_NE(n, nullptr) << c.name;
    EXPECT_EQ(n->net_type, c.type) << c.name;
  }

  const auto* v = FindVar(design, "m", "r");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 8u);
  v = FindVar(design, "m", "i");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 32u);
  v = FindVar(design, "m", "rl");
  ASSERT_NE(v, nullptr);
  EXPECT_TRUE(v->is_real);
  v = FindVar(design, "m", "tm");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 64u);
  v = FindVar(design, "m", "ev");
  ASSERT_NE(v, nullptr);
  EXPECT_TRUE(v->is_event);

  const auto* p = FindParam(design, "m", "P");
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->resolved_value, 8);
}

// Table 22-2 doing its work, likewise as structure rather than as tokens. The
// constructs are tied together on purpose: the localparam is the loop bound, so
// the count of declarations depends on it resolving, and the nested condition
// picks one iteration, so the genvar holds a different constant each pass.
TEST(SystemVerilog2012KeywordElaboration,
     IncludedVerilog2001WordsStillBuildDesign) {
  ElabFixture f;
  auto* design =
      ElaborateWithPreprocessor(In("1800-2012",
                                   "module t;\n"
                                   "  localparam L = 4;\n"
                                   "  genvar g;\n"
                                   "  reg signed   [7:0] s;\n"
                                   "  reg unsigned [7:0] u;\n"
                                   "  wire signed  [7:0] sn;\n"
                                   "  generate\n"
                                   "    for (g = 0; g < L; g = g + 1)\n"
                                   "      begin : blk\n"
                                   "        reg [7:0] slot;\n"
                                   "        if (g == 1) begin : only_one\n"
                                   "          reg [7:0] picked;\n"
                                   "        end\n"
                                   "      end\n"
                                   "  endgenerate\n"
                                   "endmodule\n"),
                                f, "t");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* l = FindParam(design, "t", "L");
  ASSERT_NE(l, nullptr);
  EXPECT_TRUE(l->is_localparam);
  EXPECT_EQ(l->resolved_value, 4);

  EXPECT_EQ(CountVarsEndingIn(design, "t", "slot"), 4u);
  EXPECT_EQ(CountVarsEndingIn(design, "t", "picked"), 1u);

  const auto* s = FindVar(design, "t", "s");
  ASSERT_NE(s, nullptr);
  EXPECT_TRUE(s->is_signed);
  const auto* u = FindVar(design, "t", "u");
  ASSERT_NE(u, nullptr);
  EXPECT_FALSE(u->is_signed);
  const auto* sn = FindNet(design, "t", "sn");
  ASSERT_NE(sn, nullptr);
  EXPECT_TRUE(sn->is_signed);
}

// The fourth included list doing its work, the largest thing this version
// inherits: data types with their widths and four-state flag, user-defined
// types with their resolved members, inferred processes each as its own kind,
// and the design element words.
TEST(SystemVerilog2012KeywordElaboration,
     IncludedSystemVerilog2005WordsStillBuildDesign) {
  const std::string kSrc =
      "package pkg;\n"
      "  localparam int WIDTH = 8;\n"
      "endpackage\n"
      "interface ifc;\n"
      "  logic [7:0] data;\n"
      "endinterface\n"
      "module ch (a, y);\n"
      "  input  [7:0] a;\n"
      "  output [7:0] y;\n"
      "  logic  [7:0] y;\n"
      "  always_comb y = a + a;\n"
      "endmodule\n"
      "module m (input logic clk, input logic d, output logic q);\n"
      "  import pkg::*;\n"
      "  ifc u_if();\n"
      "  int       counted = 21;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  typedef enum logic [1:0] {IDLE, BUSY, DONE} state_t;\n"
      "  byte_t    wide;\n"
      "  state_t   phase;\n"
      "  logic     [7:0] as_logic;\n"
      "  bit       [7:0] as_bit;\n"
      "  byte            as_byte;\n"
      "  shortint        as_shortint;\n"
      "  int             as_int;\n"
      "  longint         as_longint;\n"
      "  string          as_string;\n"
      "  chandle         as_chandle;\n"
      "  var logic [3:0] as_var;\n"
      "  logic     combo;\n"
      "  logic     latched;\n"
      "  always_comb  combo = d;\n"
      "  always_ff  @(posedge clk) q <= combo;\n"
      "  always_latch if (clk) latched = d;\n"
      "  final begin end\n"
      "  wire [7:0] ch_out;\n"
      "  ch u_ch (as_logic, ch_out);\n"
      "endmodule\n";

  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(In("1800-2012", kSrc), f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  struct TypedVar {
    const char* name;
    uint32_t width;
    bool four_state;
  };
  const TypedVar kVars[] = {
      {"as_logic", 8, true}, {"as_bit", 8, false},
      {"as_byte", 8, false}, {"as_shortint", 16, false},
      {"as_int", 32, false}, {"as_longint", 64, false},
      {"as_var", 4, true},   {"wide", 8, true},
      {"phase", 2, true},
  };
  for (const auto& c : kVars) {
    const auto* v = FindVar(design, "m", c.name);
    ASSERT_NE(v, nullptr) << c.name;
    EXPECT_EQ(v->width, c.width) << c.name;
    EXPECT_EQ(v->is_4state, c.four_state) << c.name;
  }

  const auto* s = FindVar(design, "m", "as_string");
  ASSERT_NE(s, nullptr);
  EXPECT_TRUE(s->is_string);
  const auto* h = FindVar(design, "m", "as_chandle");
  ASSERT_NE(h, nullptr);
  EXPECT_TRUE(h->is_chandle);

  const auto* m = FindModule(design, "m");
  ASSERT_NE(m, nullptr);
  auto members = m->enum_types.find("state_t");
  ASSERT_NE(members, m->enum_types.end());
  ASSERT_EQ(members->second.size(), 3u);
  EXPECT_EQ(members->second[0].name, "IDLE");
  EXPECT_EQ(members->second[0].value, 0);
  EXPECT_EQ(members->second[2].name, "DONE");
  EXPECT_EQ(members->second[2].value, 2);

  EXPECT_TRUE(HasProcess(design, "m", RtlirProcessKind::kAlwaysComb));
  EXPECT_TRUE(HasProcess(design, "m", RtlirProcessKind::kAlwaysFF));
  EXPECT_TRUE(HasProcess(design, "m", RtlirProcessKind::kAlwaysLatch));
  EXPECT_TRUE(HasProcess(design, "m", RtlirProcessKind::kFinal));

  EXPECT_EQ(design->packages.size(), 1u);
  bool wildcard_import_seen = false;
  for (const auto& imp : m->imports) {
    if (imp.package_name == "pkg" && imp.is_wildcard)
      wildcard_import_seen = true;
  }
  EXPECT_TRUE(wildcard_import_seen);
  const auto* ifc = FindModule(design, "ifc");
  ASSERT_NE(ifc, nullptr);
  EXPECT_TRUE(ifc->is_interface);

  // The declaration forms the identifier sweeps do not reach, all written with
  // types from this same list since the added words bring no ordinary data type
  // of their own: a declaration carrying its own initializer, a port typed in
  // the module header, and a port typed in the body in the separate style where
  // the header lists only names.
  const auto* counted = FindVar(design, "m", "counted");
  ASSERT_NE(counted, nullptr);
  EXPECT_EQ(counted->width, 32u);
  EXPECT_NE(counted->init_expr, nullptr);
  ASSERT_EQ(m->ports.size(), 3u);
  EXPECT_EQ(m->ports[0].type_kind, DataTypeKind::kLogic);
  EXPECT_EQ(m->ports[2].direction, Direction::kOutput);
  const auto* ch = FindModule(design, "ch");
  ASSERT_NE(ch, nullptr);
  ASSERT_EQ(ch->ports.size(), 2u);
  EXPECT_EQ(ch->ports[1].name, "y");
  EXPECT_EQ(ch->ports[1].direction, Direction::kOutput);
  const auto* y = FindVar(design, "ch", "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->width, 8u);

  ElabFixture included;
  ElaborateWithPreprocessor(In("1364-2005", kSrc), included, "m");
  EXPECT_TRUE(included.has_errors);
}

// The fifth included list doing its work: the `let` declaration lands in lists
// of its own at both scopes, the checker element resolves through an
// instantiation, the marked clocking block is counted by a rule that rejects a
// second one, and the permissive case qualifier survives into the process.
TEST(SystemVerilog2012KeywordElaboration,
     IncludedSystemVerilog2009WordsStillBuildDesign) {
  const std::string kSrc =
      "checker handshake (logic clk, logic req);\n"
      "  assert property (@(posedge clk) req);\n"
      "endchecker\n"
      "let gain = 21;\n"
      "module m (input logic clk, input logic req);\n"
      "  logic [1:0] sel;\n"
      "  logic [7:0] r;\n"
      "  let sum(untyped x, int y) = x + y;\n"
      "  global clocking gcb @(posedge clk); endclocking\n"
      "  restrict property (@(posedge clk) req);\n"
      "  handshake u_chk (clk, req);\n"
      "  initial begin\n"
      "    sel = 2'b01;\n"
      "    unique0 case (sel) 2'b01: r = 8'd1; default: r = 8'd0; endcase\n"
      "  end\n"
      "endmodule\n";

  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(In("1800-2012", kSrc), f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  bool cu_let_seen = false;
  for (auto* item : design->cu_let_decls) {
    if (item->kind == ModuleItemKind::kLetDecl && item->name == "gain")
      cu_let_seen = true;
  }
  EXPECT_TRUE(cu_let_seen);

  const auto* m = FindModule(design, "m");
  ASSERT_NE(m, nullptr);
  bool module_let_seen = false;
  for (auto* item : m->let_decls) {
    if (item->kind == ModuleItemKind::kLetDecl && item->name == "sum") {
      ASSERT_EQ(item->func_args.size(), 2u);
      EXPECT_EQ(item->func_args[0].data_type.kind, DataTypeKind::kImplicit);
      EXPECT_EQ(item->func_args[1].data_type.kind, DataTypeKind::kInt);
      module_let_seen = true;
    }
  }
  EXPECT_TRUE(module_let_seen);

  bool instance_seen = false;
  for (const auto& child : m->children) {
    if (child.inst_name == "u_chk") {
      EXPECT_EQ(child.module_name, "handshake");
      instance_seen = true;
    }
  }
  EXPECT_TRUE(instance_seen);

  bool qualified_case_seen = false;
  for (const auto& proc : m->processes) {
    if (proc.kind != RtlirProcessKind::kInitial || proc.body == nullptr)
      continue;
    for (auto* s : proc.body->stmts) {
      if (s != nullptr && s->kind == StmtKind::kCase) {
        EXPECT_EQ(s->qualifier, CaseQualifier::kUnique0);
        qualified_case_seen = true;
      }
    }
  }
  EXPECT_TRUE(qualified_case_seen);

  // The rule that counts the mark on a clocking block: a second marked block in
  // the same scope is rejected.
  ElabFixture two_global;
  ElaborateWithPreprocessor(
      In("1800-2012",
         "module m (input logic clk);\n"
         "  global clocking gcb  @(posedge clk); endclocking\n"
         "  global clocking gcb2 @(negedge clk); endclocking\n"
         "endmodule\n"),
      two_global, "m");
  EXPECT_TRUE(two_global.has_errors);

  ElabFixture included;
  ElaborateWithPreprocessor(In("1800-2005", kSrc), included, "m");
  EXPECT_TRUE(included.has_errors);
}

// The constant forms that reach a declaration's width, which is where a
// constant expression is actually required. A literal and a `parameter` come
// from the first included list, `localparam` and the `automatic` that lets a
// constant function be written from the second, and `int` from the fourth. The
// fifth form, a genvar, shows its value in the copies its loop produces and is
// observed doing that in IncludedVerilog2001WordsStillBuildDesign above.
TEST(SystemVerilog2012KeywordElaboration,
     EveryConstantFormResolvesUnderThisVersion) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      In("1800-2012",
         "module t;\n"
         "  parameter  int  P = 8;\n"
         "  localparam byte L = 8;\n"
         "  function automatic int width_of(input int n);\n"
         "    width_of = n;\n"
         "  endfunction\n"
         "  logic [7:0]             from_literal;\n"
         "  logic [P-1:0]           from_parameter;\n"
         "  logic [L-1:0]           from_localparam;\n"
         "  logic [width_of(8)-1:0] from_function;\n"
         "endmodule\n"),
      f, "t");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* p = FindParam(design, "t", "P");
  ASSERT_NE(p, nullptr);
  EXPECT_FALSE(p->is_localparam);
  EXPECT_EQ(p->resolved_value, 8);
  const auto* l = FindParam(design, "t", "L");
  ASSERT_NE(l, nullptr);
  EXPECT_TRUE(l->is_localparam);
  EXPECT_EQ(l->resolved_value, 8);

  const char* kNames[] = {"from_literal", "from_parameter", "from_localparam",
                          "from_function"};
  for (const char* name : kNames) {
    const auto* v = FindVar(design, "t", name);
    ASSERT_NE(v, nullptr) << name;
    EXPECT_EQ(v->width, 8u) << name;
  }
}

// The negative the six tables imply, carried to this stage. A word none of them
// lists is an ordinary identifier here, so it names an object that reaches the
// design -- and it is not a data type, the half that would go unchecked if only
// the naming side were tested. Each word is a near miss of a real entry, since
// this version is the last that reserves anything new.
TEST(SystemVerilog2012KeywordElaboration,
     WordsOutsideTheTablesNameObjectsButAreNotTypes) {
  const char* kNotWords[] = {
      "implement", "implements_", "interconnects", "nettypes",
      "net_type",  "softly",      "soft_",
  };
  for (const char* word : kNotWords) {
    ElabFixture named;
    auto* design =
        ElaborateWithPreprocessor(In("1800-2012", VarDecl(word)), named, "m");
    ASSERT_NE(design, nullptr) << word;
    EXPECT_FALSE(named.has_errors) << word;
    const auto* v = FindVar(design, "m", word);
    ASSERT_NE(v, nullptr) << word;
    EXPECT_EQ(v->width, 8u) << word;

    ElabFixture as_type;
    ElaborateWithPreprocessor(
        In("1800-2012",
           std::string("module m;\n  ") + word + " [7:0] v;\nendmodule\n"),
        as_type, "m");
    EXPECT_TRUE(as_type.has_errors)
        << word << " is not a data type under this version";
  }
}

}  // namespace
