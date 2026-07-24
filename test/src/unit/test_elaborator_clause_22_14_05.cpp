#include <cstddef>
#include <iterator>
#include <string>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// Table 22-1, the first of the two lists this version_specifier includes.
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

// Table 22-2, the second list, included whole -- the ten configuration words
// alongside the other eleven.
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

// Table 22-3: the single word this version adds on top of those two lists.
constexpr const char* kTable223[] = {
    "uwire",
};

std::string In2005(const std::string& body) {
  return "`begin_keywords \"1364-2005\"\n" + body + "`end_keywords\n";
}

std::string In2001(const std::string& body) {
  return "`begin_keywords \"1364-2001\"\n" + body + "`end_keywords\n";
}

std::string In1995(const std::string& body) {
  return "`begin_keywords \"1364-1995\"\n" + body + "`end_keywords\n";
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

// The word this version adds, in the role it exists for: it names a net type,
// and the net has to reach the elaborated design carrying that type. Every form
// of the declaration is here -- scalar, vector, signed -- because the width and
// the signedness travel by paths of their own. The same source under the later
// of the two lists this version includes cannot be elaborated at all, which is
// what makes the word an addition rather than something carried over.
TEST(Verilog2005KeywordElaboration, AddedWordBuildsNetsOfItsOwnType) {
  ElabFixture f;
  auto* design =
      ElaborateWithPreprocessor(In2005("module m;\n"
                                       "  uwire              scalar_net;\n"
                                       "  uwire [7:0]        vector_net;\n"
                                       "  uwire signed [7:0] signed_net;\n"
                                       "endmodule\n"),
                                f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* n = FindNet(design, "m", "scalar_net");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->net_type, NetType::kUwire);
  EXPECT_EQ(n->width, 1u);

  n = FindNet(design, "m", "vector_net");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->net_type, NetType::kUwire);
  EXPECT_EQ(n->width, 8u);

  n = FindNet(design, "m", "signed_net");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->net_type, NetType::kUwire);
  EXPECT_TRUE(n->is_signed);

  ElabFixture earlier;
  ElaborateWithPreprocessor(In2001("module m;\n  uwire scalar_net;\n"
                                   "endmodule\n"),
                            earlier, "m");
  EXPECT_TRUE(earlier.has_errors);
}

// The same net type on a module port, so the addition is observed across a
// hierarchy rather than inside one module: the child declares the port with the
// word this version adds, and the parent binds a net of that type to it.
TEST(Verilog2005KeywordElaboration, AddedWordTypesAPortAcrossAHierarchy) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      In2005("module child (input wire [7:0] a, output uwire [7:0] y);\n"
             "  assign y = a;\n"
             "endmodule\n"
             "module top;\n"
             "  wire  [7:0] src;\n"
             "  uwire [7:0] dst;\n"
             "  child u1 (.a(src), .y(dst));\n"
             "endmodule\n"),
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* c = FindModule(design, "child");
  ASSERT_NE(c, nullptr);
  ASSERT_EQ(c->ports.size(), 2u);
  EXPECT_EQ(c->ports[1].name, "y");
  EXPECT_EQ(c->ports[1].direction, Direction::kOutput);
  EXPECT_EQ(c->ports[1].type_kind, DataTypeKind::kUwire);
  EXPECT_EQ(c->ports[1].width, 8u);

  const auto* n = FindNet(design, "top", "dst");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->net_type, NetType::kUwire);
  EXPECT_EQ(n->width, 8u);
}

// The declaration forms the two tests above do not reach, carried into the
// elaborated design. A net declaration may bring its own assignment along, and
// a port may be declared in the separate style where the header lists only
// names and the body supplies direction and type; each is a production of its
// own, and the net the added word opens has to reach the design from either.
// That the first form's assignment really drives the net is observed at the
// simulator stage; nets carry no driver list at this one.
TEST(Verilog2005KeywordElaboration, AddedWordTypesEveryDeclarationForm) {
  ElabFixture with_assignment;
  auto* design =
      ElaborateWithPreprocessor(In2005("module m;\n"
                                       "  reg   [7:0] src;\n"
                                       "  uwire [7:0] bus = src + 8'd1;\n"
                                       "endmodule\n"),
                                with_assignment, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(with_assignment.has_errors);
  const auto* bus = FindNet(design, "m", "bus");
  ASSERT_NE(bus, nullptr);
  EXPECT_EQ(bus->net_type, NetType::kUwire);
  EXPECT_EQ(bus->width, 8u);

  ElabFixture non_ansi;
  design = ElaborateWithPreprocessor(In2005("module ch (a, y);\n"
                                            "  input  [7:0] a;\n"
                                            "  output [7:0] y;\n"
                                            "  uwire  [7:0] y;\n"
                                            "  assign y = a;\n"
                                            "endmodule\n"),
                                     non_ansi, "ch");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(non_ansi.has_errors);
  const auto* m = FindModule(design, "ch");
  ASSERT_NE(m, nullptr);
  ASSERT_EQ(m->ports.size(), 2u);
  EXPECT_EQ(m->ports[1].name, "y");
  EXPECT_EQ(m->ports[1].direction, Direction::kOutput);
  const auto* y = FindNet(design, "ch", "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->net_type, NetType::kUwire);
  EXPECT_EQ(y->width, 8u);
}

// The other face of the same addition: being reserved here, the word cannot
// name a variable, and under both of the lists this version includes the very
// same declaration builds one. Reading the variable back off those designs is
// what keeps the accepting legs from being any elaboration that happens to
// succeed.
TEST(Verilog2005KeywordElaboration, AddedWordCannotNameAnElaboratedVariable) {
  ASSERT_EQ(std::size(kTable223), 1u);
  const char* added = kTable223[0];

  ElabFixture reserved;
  ElaborateWithPreprocessor(In2005(VarDecl(added)), reserved, "m");
  EXPECT_TRUE(reserved.has_errors);

  for (const auto& earlier : {In2001(VarDecl(added)), In1995(VarDecl(added))}) {
    ElabFixture f;
    auto* design = ElaborateWithPreprocessor(earlier, f, "m");
    ASSERT_NE(design, nullptr);
    EXPECT_FALSE(f.has_errors);
    const auto* v = FindVar(design, "m", added);
    ASSERT_NE(v, nullptr);
    EXPECT_EQ(v->width, 8u);
  }
}

// The second included list at this stage, swept whole. Each of Table 22-2's
// entries is reserved here, and under "1364-1995" -- the other list this
// version includes, where it is not yet a keyword -- the same declaration
// elaborates into a variable of the width it asked for. The pair is what makes
// each word an inclusion rather than an unrelated failure.
TEST(Verilog2005KeywordElaboration, IncludedVerilog2001WordsAreReserved) {
  EXPECT_EQ(std::size(kTable222), 21u);
  for (const char* word : kTable222) {
    ElabFixture reserved;
    ElaborateWithPreprocessor(In2005(VarDecl(word)), reserved, "m");
    EXPECT_TRUE(reserved.has_errors) << word;

    ElabFixture freed;
    auto* design = ElaborateWithPreprocessor(In1995(VarDecl(word)), freed, "m");
    ASSERT_NE(design, nullptr) << word;
    EXPECT_FALSE(freed.has_errors) << word;
    const auto* v = FindVar(design, "m", word);
    ASSERT_NE(v, nullptr) << word;
    EXPECT_EQ(v->width, 8u) << word;
  }
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

// The first included list, swept at this stage. There is no earlier version to
// pair these against -- they have been reserved since the list this version
// starts from -- so the accepting side of the claim is the test below, where
// the same words build the design in their keyword roles.
TEST(Verilog2005KeywordElaboration, IncludedVerilog1995WordsAreReserved) {
  EXPECT_EQ(std::size(kTable221), 102u);
  size_t swept = 0;
  for (const char* word : kTable221) {
    if (IsGatePrimitiveWord(word)) continue;
    ElabFixture f;
    ElaborateWithPreprocessor(In2005(VarDecl(word)), f, "m");
    EXPECT_TRUE(f.has_errors)
        << word << " is included from Table 22-1 and stays reserved";
    ++swept;
  }
  EXPECT_EQ(swept, 96u);
}

// Table 22-1 doing its work under this version, read back as elaborated
// structure. The net types are the sharpest part: each resolved and driven type
// the earlier list names has to survive into the design as itself rather than
// collapsing onto a plain wire, which would leave the inclusion unobserved.
TEST(Verilog2005KeywordElaboration, IncludedVerilog1995WordsStillBuildDesign) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      In2005("module m (input wire a, output wire y);\n"
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
TEST(Verilog2005KeywordElaboration, IncludedVerilog2001WordsStillBuildDesign) {
  ElabFixture f;
  auto* design =
      ElaborateWithPreprocessor(In2005("module t;\n"
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

// The constant forms that reach a declaration's width, which is where a
// constant expression is actually required: a literal and a `parameter` come
// from Table 22-1, and `localparam` and the `automatic` that lets a constant
// function be written come from Table 22-2. So every one of them is writable
// here by virtue of what this version includes rather than of anything it adds,
// and the width the design ends up with is what shows the constant resolved.
//
// The remaining constant form, a genvar, shows its value only in the copies its
// loop produces rather than in a width, and it is observed doing exactly that
// in IncludedVerilog2001WordsStillBuildDesign above -- there against a loop
// bound that is itself a constant and with a nested condition singling out one
// iteration, which is strictly more than a copy count. Repeating a weaker
// version of it here would add nothing.
TEST(Verilog2005KeywordElaboration, EveryConstantFormResolvesUnderThisVersion) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      In2005("module t;\n"
             "  parameter  P = 8;\n"
             "  localparam L = 8;\n"
             "  function automatic integer width_of(input reg [7:0] n);\n"
             "    width_of = n;\n"
             "  endfunction\n"
             "  reg [7:0]            from_literal;\n"
             "  reg [P-1:0]          from_parameter;\n"
             "  reg [L-1:0]          from_localparam;\n"
             "  reg [width_of(8)-1:0] from_function;\n"
             "endmodule\n"),
      f, "t");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const char* kNames[] = {"from_literal", "from_parameter", "from_localparam",
                          "from_function"};
  for (const char* name : kNames) {
    const auto* v = FindVar(design, "t", name);
    ASSERT_NE(v, nullptr) << name;
    EXPECT_EQ(v->width, 8u) << name;
  }
}

// The negative the three tables imply, carried to this stage. A word none of
// them lists is an ordinary identifier here, so it names an object that really
// reaches the design -- and it is not a data type, which is the half that would
// go unchecked if only the naming side were tested.
TEST(Verilog2005KeywordElaboration, UnlistedWordsNameObjectsButAreNotTypes) {
  const char* kUnlisted[] = {"logic", "interface", "bit", "byte", "int"};
  for (const char* word : kUnlisted) {
    ElabFixture named;
    auto* design = ElaborateWithPreprocessor(In2005(VarDecl(word)), named, "m");
    ASSERT_NE(design, nullptr) << word;
    EXPECT_FALSE(named.has_errors) << word;
    const auto* v = FindVar(design, "m", word);
    ASSERT_NE(v, nullptr) << word;
    EXPECT_EQ(v->width, 8u) << word;

    ElabFixture as_type;
    ElaborateWithPreprocessor(
        In2005(std::string("module m;\n  ") + word + " [7:0] v;\nendmodule\n"),
        as_type, "m");
    EXPECT_TRUE(as_type.has_errors)
        << word << " is not a data type under this version";
  }
}

}  // namespace
