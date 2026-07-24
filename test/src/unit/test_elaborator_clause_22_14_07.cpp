#include <cstddef>
#include <iterator>
#include <string>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// Table 22-1, the first of the four lists this version_specifier includes.
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

// Table 22-2, the second included list -- included whole, the ten configuration
// words alongside the other eleven.
constexpr const char* kTable222[] = {
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

// The ten of Table 22-2 the configuration-free companion list drops. They are
// what separates the two lists published for the same standard, so they settle
// which of the two "all previous versions" brings in.
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

// Table 22-5: what this version adds on top of the four lists it includes.
constexpr const char* kTable225[] = {
    "accept_on",      "checker",        "endchecker",   "eventually",
    "global",         "implies",        "let",          "nexttime",
    "reject_on",      "restrict",       "s_always",     "s_eventually",
    "s_nexttime",     "s_until",        "s_until_with", "strong",
    "sync_accept_on", "sync_reject_on", "unique0",      "until",
    "until_with",     "untyped",        "weak",
};

std::string InSv2009(const std::string& body) {
  return "`begin_keywords \"1800-2009\"\n" + body + "`end_keywords\n";
}

// "1800-2005" is the union of the four lists this version includes, so it is
// the leg every Table 22-5 claim is measured against: a word free there and
// reserved here was added by this version_specifier.
std::string InSv2005(const std::string& body) {
  return "`begin_keywords \"1800-2005\"\n" + body + "`end_keywords\n";
}

std::string In2005(const std::string& body) {
  return "`begin_keywords \"1364-2005\"\n" + body + "`end_keywords\n";
}

std::string In2001(const std::string& body) {
  return "`begin_keywords \"1364-2001\"\n" + body + "`end_keywords\n";
}

std::string InNoconfig(const std::string& body) {
  return "`begin_keywords \"1364-2001-noconfig\"\n" + body + "`end_keywords\n";
}

std::string In1995(const std::string& body) {
  return "`begin_keywords \"1364-1995\"\n" + body + "`end_keywords\n";
}

// The specifier for the standard published after this one, used only to show
// that the words this version leaves free are ones a later list claims.
std::string InSv2012(const std::string& body) {
  return "`begin_keywords \"1800-2012\"\n" + body + "`end_keywords\n";
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

// How many elaborated variables in `mod` have a name ending in `suffix`, used
// to observe a loop generate construct without depending on how the elaborator
// spells a per-iteration name.
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
// slot holds one of them is read as a malformed instantiation. Elaborating that
// crashes, with or without any `begin_keywords region and under the default
// reserved word list too, so the fault is not this subclause's and no test here
// can drive it. These six are swept in the identifier slot at the parser stage
// instead, where the same source is rejected without incident.
bool IsGatePrimitiveWord(const std::string& word) {
  const char* kGates[] = {"and", "nand", "nor", "or", "xnor", "xor"};
  for (const char* g : kGates) {
    if (word == g) return true;
  }
  return false;
}

// Two of Table 22-4's entries open an aggregate type declaration, and a
// declaration whose identifier slot holds one of them is read as the start of
// such a type. The parser does not terminate on that -- with no directive in
// force either -- so the elaborator is never reached and no test here can drive
// those two. They are swept in the identifier slot at the lexer and
// preprocessor stages instead, where the list is observed without parsing.
bool IsAggregateOpenerWord(const std::string& word) {
  return word == "struct" || word == "union";
}

// The first included list, swept at this stage. There is no earlier version to
// pair these against -- they have been reserved since the first of the four
// lists this version names -- so the accepting side of the claim is the test
// below, where the same words build the design in their keyword roles.
TEST(SystemVerilog2009KeywordElaboration, IncludedVerilog1995WordsAreReserved) {
  EXPECT_EQ(std::size(kTable221), 102u);
  size_t swept = 0;
  for (const char* word : kTable221) {
    if (IsGatePrimitiveWord(word)) continue;
    ElabFixture f;
    ElaborateWithPreprocessor(InSv2009(VarDecl(word)), f, "m");
    EXPECT_TRUE(f.has_errors)
        << word << " is included from Table 22-1 and stays reserved";
    ++swept;
  }
  EXPECT_EQ(swept, 96u);
}

// The second included list at this stage, swept whole. Each of Table 22-2's
// entries is reserved here, and under "1364-1995" -- the first of the four
// lists this version includes, where it is not yet a keyword -- the same
// declaration elaborates into a variable of the width it asked for. The ten
// configuration words carry a second accepting leg, under the companion list
// that drops exactly them, which is how this stage shows the full list is what
// gets inherited.
TEST(SystemVerilog2009KeywordElaboration, IncludedVerilog2001WordsAreReserved) {
  EXPECT_EQ(std::size(kTable222), 21u);
  for (const char* word : kTable222) {
    ElabFixture reserved;
    ElaborateWithPreprocessor(InSv2009(VarDecl(word)), reserved, "m");
    EXPECT_TRUE(reserved.has_errors) << word;

    ElabFixture freed;
    auto* design = ElaborateWithPreprocessor(In1995(VarDecl(word)), freed, "m");
    ASSERT_NE(design, nullptr) << word;
    EXPECT_FALSE(freed.has_errors) << word;
    const auto* v = FindVar(design, "m", word);
    ASSERT_NE(v, nullptr) << word;
    EXPECT_EQ(v->width, 8u) << word;
  }

  EXPECT_EQ(std::size(kConfigurationWords), 10u);
  for (const char* word : kConfigurationWords) {
    ElabFixture dropped;
    auto* design =
        ElaborateWithPreprocessor(InNoconfig(VarDecl(word)), dropped, "m");
    ASSERT_NE(design, nullptr) << word;
    EXPECT_FALSE(dropped.has_errors) << word;
    const auto* v = FindVar(design, "m", word);
    ASSERT_NE(v, nullptr) << word;
    EXPECT_EQ(v->width, 8u) << word;
  }
}

// The third included list. Its one word cannot name an elaborated variable
// here, names one under both of the lists the version it comes from is built
// on, and still carries its net type into the design -- inclusion means the
// keyword role survives, not only that the identifier slot closes.
TEST(SystemVerilog2009KeywordElaboration, IncludedVerilog2005WordIsReserved) {
  ASSERT_EQ(std::size(kTable223), 1u);
  const char* word = kTable223[0];

  ElabFixture reserved;
  ElaborateWithPreprocessor(InSv2009(VarDecl(word)), reserved, "m");
  EXPECT_TRUE(reserved.has_errors);

  for (const auto& earlier : {In2001(VarDecl(word)), In1995(VarDecl(word))}) {
    ElabFixture f;
    auto* design = ElaborateWithPreprocessor(earlier, f, "m");
    ASSERT_NE(design, nullptr);
    EXPECT_FALSE(f.has_errors);
    const auto* v = FindVar(design, "m", word);
    ASSERT_NE(v, nullptr);
    EXPECT_EQ(v->width, 8u);
  }

  ElabFixture as_net;
  auto* design =
      ElaborateWithPreprocessor(InSv2009("module m;\n"
                                         "  uwire       scalar_net;\n"
                                         "  uwire [7:0] vector_net;\n"
                                         "endmodule\n"),
                                as_net, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(as_net.has_errors);
  const auto* n = FindNet(design, "m", "scalar_net");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->net_type, NetType::kUwire);
  EXPECT_EQ(n->width, 1u);
  n = FindNet(design, "m", "vector_net");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->net_type, NetType::kUwire);
  EXPECT_EQ(n->width, 8u);
}

// The fourth included list swept whole at this stage. Each entry is reserved
// here and, under "1364-2005" -- the union of the three lists that one is
// itself built on -- the same declaration reaches the design as a variable of
// the width it asked for, so the inclusion traces to the fourth list.
TEST(SystemVerilog2009KeywordElaboration,
     IncludedSystemVerilog2005WordsAreReserved) {
  EXPECT_EQ(std::size(kTable224), 97u);
  size_t swept = 0;
  for (const char* word : kTable224) {
    if (IsAggregateOpenerWord(word)) continue;

    ElabFixture reserved;
    ElaborateWithPreprocessor(InSv2009(VarDecl(word)), reserved, "m");
    EXPECT_TRUE(reserved.has_errors) << word;

    ElabFixture freed;
    auto* design = ElaborateWithPreprocessor(In2005(VarDecl(word)), freed, "m");
    ASSERT_NE(design, nullptr) << word;
    EXPECT_FALSE(freed.has_errors) << word;
    const auto* v = FindVar(design, "m", word);
    ASSERT_NE(v, nullptr) << word;
    EXPECT_EQ(v->width, 8u) << word;
    ++swept;
  }
  EXPECT_EQ(swept, 95u);
}

// Table 22-5 swept whole at this stage, with the leg that makes each entry an
// addition. The word cannot name an elaborated variable here, and under
// "1800-2005" -- the union of everything this version includes -- the same
// declaration reaches the design as a variable of the width it asked for.
// Reading the variable back is what keeps the accepting leg from being any
// elaboration that happens to succeed.
TEST(SystemVerilog2009KeywordElaboration, AddedWordsCannotNameVariables) {
  EXPECT_EQ(std::size(kTable225), 23u);
  for (const char* word : kTable225) {
    ElabFixture reserved;
    ElaborateWithPreprocessor(InSv2009(VarDecl(word)), reserved, "m");
    EXPECT_TRUE(reserved.has_errors) << word;

    ElabFixture freed;
    auto* design =
        ElaborateWithPreprocessor(InSv2005(VarDecl(word)), freed, "m");
    ASSERT_NE(design, nullptr) << word;
    EXPECT_FALSE(freed.has_errors) << word;
    const auto* v = FindVar(design, "m", word);
    ASSERT_NE(v, nullptr) << word;
    EXPECT_EQ(v->width, 8u) << word;
  }
}

// The added word whose construct the elaborator carries into the design in a
// list of its own. A `let` declaration may be written at the compilation unit's
// scope or inside a design element, and the two land in different places, so
// both are here. The declaration is the only Table 22-5 construct that becomes
// elaborated structure rather than staying inside a statement or a property
// body, which is why it carries this stage's addition claim.
TEST(SystemVerilog2009KeywordElaboration, AddedLetDeclarationsReachTheDesign) {
  const std::string kSrc =
      "let gain = 21;\n"
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] r;\n"
      "  let sum(untyped x, int y) = x + y;\n"
      "  initial r = sum(a, gain);\n"
      "endmodule\n";

  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(InSv2009(kSrc), f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  bool cu_let_seen = false;
  for (auto* item : design->cu_let_decls) {
    if (item->kind == ModuleItemKind::kLetDecl && item->name == "gain") {
      cu_let_seen = true;
    }
  }
  EXPECT_TRUE(cu_let_seen);

  const auto* m = FindModule(design, "m");
  ASSERT_NE(m, nullptr);
  bool module_let_seen = false;
  for (auto* item : m->let_decls) {
    if (item->kind == ModuleItemKind::kLetDecl && item->name == "sum") {
      // The `untyped` formal is left without a data type while its typed
      // neighbour keeps one -- the two added words are observed together.
      ASSERT_EQ(item->func_args.size(), 2u);
      EXPECT_EQ(item->func_args[0].data_type.kind, DataTypeKind::kImplicit);
      EXPECT_EQ(item->func_args[1].data_type.kind, DataTypeKind::kInt);
      module_let_seen = true;
    }
  }
  EXPECT_TRUE(module_let_seen);

  ElabFixture included;
  ElaborateWithPreprocessor(InSv2005(kSrc), included, "m");
  EXPECT_TRUE(included.has_errors);
}

// The added word pair that brackets a design element. A checker is elaborated
// through an instantiation inside a module, so the instance has to resolve to
// the element `checker`/`endchecker` opened -- something no other Table 22-5
// word reaches, since the rest name statements, operators, or qualifiers. The
// body is written with the assertion vocabulary of the fourth included list, so
// the inclusion and the addition are observed working together.
TEST(SystemVerilog2009KeywordElaboration, AddedCheckerElementIsInstantiable) {
  const std::string kSrc =
      "checker handshake (logic clk, logic req);\n"
      "  assert property (@(posedge clk) req);\n"
      "endchecker\n"
      "module m;\n"
      "  logic clk;\n"
      "  logic req;\n"
      "  handshake u_chk (clk, req);\n"
      "endmodule\n";

  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(InSv2009(kSrc), f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* m = FindModule(design, "m");
  ASSERT_NE(m, nullptr);
  bool instance_seen = false;
  for (const auto& child : m->children) {
    if (child.inst_name == "u_chk") {
      EXPECT_EQ(child.module_name, "handshake");
      instance_seen = true;
    }
  }
  EXPECT_TRUE(instance_seen);

  ElabFixture included;
  ElaborateWithPreprocessor(InSv2005(kSrc), included, "m");
  EXPECT_TRUE(included.has_errors);
}

// The added word whose effect the elaborator itself acts on. `global` marks a
// clocking block as the one such block a scope may have, and two elaborator
// rules turn on that mark: a second one in the same scope is rejected, and a
// reference to the global clock is only resolvable when a block carrying the
// mark is in scope. Both are driven from real source here, and each is shown
// both ways round -- a plain clocking block alongside a global one is fine
// while two global ones are not, and the same global-clock reference resolves
// with the block present and fails without it. That is the elaborator reading
// the word, not merely tolerating it. Neither source can be written at all
// under the union of everything this version includes, where `global` is an
// ordinary identifier.
TEST(SystemVerilog2009KeywordElaboration,
     AddedGlobalClockingIsCountedAtElaboration) {
  // One marked block beside an unmarked one: the mark is what tells them apart.
  const std::string kOne =
      "module m (input logic clk);\n"
      "  global clocking gcb @(posedge clk); endclocking\n"
      "  clocking cb @(posedge clk); input clk; endclocking\n"
      "endmodule\n";
  ElabFixture one;
  auto* design = ElaborateWithPreprocessor(InSv2009(kOne), one, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(one.has_errors);

  // Two marked blocks in the same scope: rejected, which only a rule counting
  // the mark can do.
  ElabFixture two;
  ElaborateWithPreprocessor(
      InSv2009("module m (input logic clk);\n"
               "  global clocking gcb  @(posedge clk); endclocking\n"
               "  global clocking gcb2 @(negedge clk); endclocking\n"
               "endmodule\n"),
      two, "m");
  EXPECT_TRUE(two.has_errors);

  // A reference to the global clock, resolvable only because a marked block is
  // in scope.
  const std::string kReference =
      "module m (input logic clk, input logic a);\n"
      "  global clocking gcb @(posedge clk); endclocking\n"
      "  assert property (@($global_clock) a);\n"
      "endmodule\n";
  ElabFixture with_block;
  design = ElaborateWithPreprocessor(InSv2009(kReference), with_block, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(with_block.has_errors);

  ElabFixture without_block;
  ElaborateWithPreprocessor(
      InSv2009("module m (input logic clk, input logic a);\n"
               "  assert property (@($global_clock) a);\n"
               "endmodule\n"),
      without_block, "m");
  EXPECT_TRUE(without_block.has_errors);

  // The addition leg: neither source exists under the included lists.
  for (const auto& src : {kOne, kReference}) {
    ElabFixture included;
    ElaborateWithPreprocessor(InSv2005(src), included, "m");
    EXPECT_TRUE(included.has_errors);
  }
}

// The two remaining added words with a construct of their own, carried into the
// elaborated design. `unique0` qualifies a case statement, and the qualifier
// has to survive into the process the elaborator builds -- it is read back off
// that process's body rather than off the parse tree. `restrict` opens a module
// item of its own kind, and a design holding one elaborates clean alongside the
// assertion items the fourth included list already offers. Both sources are
// unwritable under the union of everything this version includes.
TEST(SystemVerilog2009KeywordElaboration,
     AddedQualifierAndRestrictConstructsReachTheDesign) {
  const std::string kSrc =
      "module m (input logic clk, input logic req);\n"
      "  logic [1:0] sel;\n"
      "  logic [7:0] r;\n"
      "  restrict property (@(posedge clk) req);\n"
      "  assert property (@(posedge clk) req);\n"
      "  initial begin\n"
      "    sel = 2'b01;\n"
      "    unique0 case (sel) 2'b01: r = 8'd1; default: r = 8'd0; endcase\n"
      "  end\n"
      "endmodule\n";

  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(InSv2009(kSrc), f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* m = FindModule(design, "m");
  ASSERT_NE(m, nullptr);
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

  ElabFixture included;
  ElaborateWithPreprocessor(InSv2005(kSrc), included, "m");
  EXPECT_TRUE(included.has_errors);
}

// Table 22-1 doing its work under this version, read back as elaborated
// structure. The net types are the sharpest part: each resolved and driven type
// the first included list names has to survive into the design as itself rather
// than collapsing onto a plain wire, which would leave the inclusion
// unobserved.
TEST(SystemVerilog2009KeywordElaboration,
     IncludedVerilog1995WordsStillBuildDesign) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      InSv2009("module m (input wire a, output wire y);\n"
               "  wand     wa;\n"
               "  wor      wo;\n"
               "  triand   ta;\n"
               "  trior    to;\n"
               "  tri0     t0;\n"
               "  tri1     t1;\n"
               "  trireg   tr;\n"
               "  supply0  gnd;\n"
               "  supply1  vdd;\n"
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
      {"wa", NetType::kWand},     {"wo", NetType::kWor},
      {"ta", NetType::kTriand},   {"to", NetType::kTrior},
      {"t0", NetType::kTri0},     {"t1", NetType::kTri1},
      {"tr", NetType::kTrireg},   {"gnd", NetType::kSupply0},
      {"vdd", NetType::kSupply1},
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

// Table 22-2 doing its work, likewise as structure rather than as tokens.
// `localparam` resolves to a constant, `genvar`/`generate`/`endgenerate`
// produce one copy of the loop body per iteration, and `signed`/`unsigned`
// select what they select. The three are tied together on purpose: the
// localparam is the loop bound, so the count of declarations reaching the
// design depends on it resolving, and the nested condition picks out a single
// iteration, so the genvar has to hold a different constant on each pass.
TEST(SystemVerilog2009KeywordElaboration,
     IncludedVerilog2001WordsStillBuildDesign) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      InSv2009("module t;\n"
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

// The fourth included list doing its work, which is the largest thing this
// version inherits. The data types are read back with their widths and with the
// four-state flag that separates the two-state additions from `reg` and
// `logic`; the user-defined types carry their widths and their resolved
// members; the inferred processes reach the design each as its own kind; and
// the design element words open elements the elaborator distinguishes. The same
// source is not a design at all under the union of the three lists that fourth
// one is itself built on.
TEST(SystemVerilog2009KeywordElaboration,
     IncludedSystemVerilog2005WordsStillBuildDesign) {
  const std::string kSrc =
      "package pkg;\n"
      "  localparam int WIDTH = 8;\n"
      "endpackage\n"
      "interface ifc;\n"
      "  logic [7:0] data;\n"
      "endinterface\n"
      "module m (input logic clk, input logic d, output logic q);\n"
      "  import pkg::*;\n"
      "  ifc u_if();\n"
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
      "endmodule\n";

  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(InSv2009(kSrc), f, "m");
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

  ElabFixture included;
  ElaborateWithPreprocessor(In2005(kSrc), included, "m");
  EXPECT_TRUE(included.has_errors);
}

// The constant forms that reach a declaration's width, which is where a
// constant expression is actually required. A literal and a `parameter` come
// from the first included list, `localparam` and the `automatic` that lets a
// constant function be written come from the second, and `int` -- the type the
// function returns and the declarations take -- comes from the fourth. So all
// four forms are reachable here only because of what this version includes, and
// the width the design ends up with is what shows each constant resolved.
//
// The remaining constant form, a genvar, shows its value in the copies its loop
// produces rather than in a width, and it is observed doing exactly that in
// IncludedVerilog2001WordsStillBuildDesign above -- there against a loop bound
// that is itself a constant and with a nested condition singling out one
// iteration. Repeating a weaker version of it here would add nothing.
TEST(SystemVerilog2009KeywordElaboration,
     EveryConstantFormResolvesUnderThisVersion) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      InSv2009("module t;\n"
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

// The declaration forms the sweeps do not reach, carried into the elaborated
// design. A declaration may bring its own initializer along, a port may be
// typed in the module header, and a port may instead be typed in the body in
// the separate style where the header lists only names. Each is a production of
// its own, and they are exercised across a hierarchy here rather than inside
// one module. All three are written with types from the fourth included list --
// this version adds no type of its own -- so what the forms show is that
// everything the additions are written alongside keeps working under the same
// region.
TEST(SystemVerilog2009KeywordElaboration, EveryDeclarationFormStillElaborates) {
  ElabFixture ansi;
  auto* design = ElaborateWithPreprocessor(
      InSv2009("module child (input logic [7:0] a, input byte b,\n"
               "              output int y);\n"
               "  assign y = a + b;\n"
               "endmodule\n"
               "module top;\n"
               "  logic [7:0] src;\n"
               "  byte        step;\n"
               "  int         dst;\n"
               "  int         counted = 21;\n"
               "  child u1 (.a(src), .b(step), .y(dst));\n"
               "endmodule\n"),
      ansi, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(ansi.has_errors);

  const auto* child = FindModule(design, "child");
  ASSERT_NE(child, nullptr);
  ASSERT_EQ(child->ports.size(), 3u);
  EXPECT_EQ(child->ports[0].type_kind, DataTypeKind::kLogic);
  EXPECT_EQ(child->ports[0].width, 8u);
  EXPECT_EQ(child->ports[1].type_kind, DataTypeKind::kByte);
  EXPECT_EQ(child->ports[1].width, 8u);
  EXPECT_EQ(child->ports[2].type_kind, DataTypeKind::kInt);
  EXPECT_EQ(child->ports[2].direction, Direction::kOutput);
  EXPECT_EQ(child->ports[2].width, 32u);

  const auto* dst = FindVar(design, "top", "dst");
  ASSERT_NE(dst, nullptr);
  EXPECT_EQ(dst->width, 32u);
  const auto* counted = FindVar(design, "top", "counted");
  ASSERT_NE(counted, nullptr);
  EXPECT_EQ(counted->width, 32u);
  EXPECT_NE(counted->init_expr, nullptr);

  ElabFixture non_ansi;
  design = ElaborateWithPreprocessor(InSv2009("module ch (a, y);\n"
                                              "  input  [7:0] a;\n"
                                              "  output [7:0] y;\n"
                                              "  logic  [7:0] y;\n"
                                              "  always_comb y = a + a;\n"
                                              "endmodule\n"),
                                     non_ansi, "ch");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(non_ansi.has_errors);
  const auto* m = FindModule(design, "ch");
  ASSERT_NE(m, nullptr);
  ASSERT_EQ(m->ports.size(), 2u);
  EXPECT_EQ(m->ports[1].name, "y");
  EXPECT_EQ(m->ports[1].direction, Direction::kOutput);
  const auto* y = FindVar(design, "ch", "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->width, 8u);
}

// The negative the five tables imply, carried to this stage. A word none of
// them lists is an ordinary identifier here, so it names an object that really
// reaches the design -- and it is not a data type, which is the half that would
// go unchecked if only the naming side were tested. Each word is one the next
// standard reserves, so what is bounded is this version's list rather than the
// vocabulary at large.
TEST(SystemVerilog2009KeywordElaboration, LaterWordsNameObjectsButAreNotTypes) {
  // None of these opens a design element, so putting one at the head of a line
  // leaves the region machinery -- which tracks design elements by a line's
  // first word, without regard to the list in force -- out of the picture, and
  // the only thing that can reject the source is the word not being a type.
  const char* kLater[] = {"implements", "interconnect", "nettype", "soft"};
  for (const char* word : kLater) {
    ElabFixture named;
    auto* design =
        ElaborateWithPreprocessor(InSv2009(VarDecl(word)), named, "m");
    ASSERT_NE(design, nullptr) << word;
    EXPECT_FALSE(named.has_errors) << word;
    const auto* v = FindVar(design, "m", word);
    ASSERT_NE(v, nullptr) << word;
    EXPECT_EQ(v->width, 8u) << word;

    ElabFixture as_type;
    ElaborateWithPreprocessor(InSv2009(std::string("module m;\n  ") + word +
                                       " [7:0] v;\nendmodule\n"),
                              as_type, "m");
    EXPECT_TRUE(as_type.has_errors)
        << word << " is not a data type under this version";

    // The leg that makes each of these a *later* word rather than one this
    // implementation simply does not know: the specifier for the standard after
    // this one reserves it, so the same declaration never reaches a design
    // there. That is what places the boundary of this version's list between
    // the two.
    ElabFixture later;
    ElaborateWithPreprocessor(InSv2012(VarDecl(word)), later, "m");
    EXPECT_TRUE(later.has_errors)
        << word << " is reserved by the version after this one";
  }
}

}  // namespace
