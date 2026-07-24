#include <cstddef>
#include <string>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// Table 22-2: the identifiers "1364-2001" adds to the list it inherits.
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

// Wraps `body` in a real `begin_keywords "1364-2001" region, so the reserved
// word list this version names is the one in force while the design is built.
std::string In2001(const std::string& body) {
  return "`begin_keywords \"1364-2001\"\n" + body + "`end_keywords\n";
}

std::string In1995(const std::string& body) {
  return "`begin_keywords \"1364-1995\"\n" + body + "`end_keywords\n";
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

// The additions of this version doing their elaborated job rather than merely
// lexing as keywords: `localparam` produces a resolved constant, and
// `genvar`/`generate`/`endgenerate` produce one copy of the loop body per
// iteration. The three are tied together deliberately. The localparam is the
// loop bound, so the number of declarations reaching the design can only come
// out right if it resolved; and the nested condition picks out a single
// iteration, so the genvar has to hold a different constant on each pass rather
// than merely make the loop run the right number of times.
TEST(Verilog2001KeywordElaboration, LocalparamAndGenerateBuildTheDesign) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      In2001("module t;\n"
             "  localparam L = 4;\n"
             "  genvar g;\n"
             "  generate\n"
             "    for (g = 0; g < L; g = g + 1) begin : blk\n"
             "      reg [7:0] slot;\n"
             "      if (g == 1) begin : only_one\n"
             "        reg [7:0] picked;\n"
             "      end\n"
             "    end\n"
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
}

// A declaration's width can come from any of the constant forms, and each
// reaches the elaborator by a different path. This version is the first whose
// list makes them all writable at once: the literal and the `parameter` are
// inherited, while `localparam` and the `automatic` function whose call is
// folded are both additions. Every form has to arrive at the same width. The
// remaining constant form, a genvar, is covered by the loop generate test
// above.
TEST(Verilog2001KeywordElaboration, ConstantFormsAllProduceTheSameWidth) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      In2001("module t;\n"
             "  parameter  P = 8;\n"
             "  localparam L = 8;\n"
             "  function automatic integer widthof(input reg [7:0] n);\n"
             "    widthof = n;\n"
             "  endfunction\n"
             "  reg [7:0]            from_literal;\n"
             "  reg [P-1:0]          from_parameter;\n"
             "  reg [L-1:0]          from_localparam;\n"
             "  reg [widthof(8)-1:0] from_function;\n"
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

// `signed` and `unsigned` are additions of this version, and what they select
// survives into the design: the same declared width, differing only in the
// signedness the keyword asked for.
TEST(Verilog2001KeywordElaboration, SignedAndUnsignedSelectSignedness) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(In2001("module t;\n"
                                                  "  reg signed   [7:0] s;\n"
                                                  "  reg unsigned [7:0] u;\n"
                                                  "  wire signed  [7:0] n;\n"
                                                  "endmodule\n"),
                                           f, "t");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* s = FindVar(design, "t", "s");
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(s->width, 8u);
  EXPECT_TRUE(s->is_signed);

  const auto* u = FindVar(design, "t", "u");
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(u->width, 8u);
  EXPECT_FALSE(u->is_signed);

  const auto* n = FindNet(design, "t", "n");
  ASSERT_NE(n, nullptr);
  EXPECT_TRUE(n->is_signed);
}

// The inclusion half at this stage: the variable and net type keywords the
// earlier list names still declare their own storage under this one, each with
// the width, the real/vector distinction, and the net type its own type
// implies.
TEST(Verilog2001KeywordElaboration, InheritedTypeKeywordsKeepTheirStorage) {
  struct VarCase {
    const char* decl;
    uint32_t width;
    bool is_real;
  };
  const VarCase kVarCases[] = {
      {"reg v;", 1, false},      {"reg [15:0] v;", 16, false},
      {"integer v;", 32, false}, {"time v;", 64, false},
      {"real v;", 64, true},     {"realtime v;", 64, true},
  };
  for (const auto& c : kVarCases) {
    ElabFixture f;
    auto* design = ElaborateWithPreprocessor(
        In2001(std::string("module t;\n  ") + c.decl + "\nendmodule\n"), f,
        "t");
    ASSERT_NE(design, nullptr) << c.decl;
    EXPECT_FALSE(f.has_errors) << c.decl;

    const auto* v = FindVar(design, "t", "v");
    ASSERT_NE(v, nullptr) << c.decl;
    EXPECT_EQ(v->width, c.width) << c.decl;
    EXPECT_EQ(v->is_real, c.is_real) << c.decl;
  }

  struct NetCase {
    const char* decl;
    NetType type;
  };
  const NetCase kNetCases[] = {
      {"wand n;", NetType::kWand},       {"wor n;", NetType::kWor},
      {"triand n;", NetType::kTriand},   {"trior n;", NetType::kTrior},
      {"tri0 n;", NetType::kTri0},       {"tri1 n;", NetType::kTri1},
      {"trireg n;", NetType::kTrireg},   {"supply0 n;", NetType::kSupply0},
      {"supply1 n;", NetType::kSupply1}, {"tri n;", NetType::kTri},
  };
  for (const auto& c : kNetCases) {
    ElabFixture f;
    auto* design = ElaborateWithPreprocessor(
        In2001(std::string("module t;\n  ") + c.decl + "\nendmodule\n"), f,
        "t");
    ASSERT_NE(design, nullptr) << c.decl;
    EXPECT_FALSE(f.has_errors) << c.decl;

    const auto* n = FindNet(design, "t", "n");
    ASSERT_NE(n, nullptr) << c.decl;
    EXPECT_EQ(n->net_type, c.type) << c.decl;
  }
}

// Words neither table lists are ordinary identifiers under this version, and
// they stay ordinary identifiers all the way into the elaborated design: each
// names a variable that really exists there, carrying the storage its
// declaration asked for. Getting past the parser is not enough -- the design is
// what the rest of the tool works from.
TEST(Verilog2001KeywordElaboration, FreedWordsNameElaboratedVariables) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(In2001("module m;\n"
                                                  "  reg [63:0] logic;\n"
                                                  "  reg [7:0]  bit;\n"
                                                  "  integer    int;\n"
                                                  "  real       shortreal;\n"
                                                  "  time       longint;\n"
                                                  "  event      package;\n"
                                                  "endmodule\n"),
                                           f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* v = FindVar(design, "m", "logic");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 64u);

  v = FindVar(design, "m", "bit");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 8u);

  v = FindVar(design, "m", "int");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 32u);

  v = FindVar(design, "m", "shortreal");
  ASSERT_NE(v, nullptr);
  EXPECT_TRUE(v->is_real);

  v = FindVar(design, "m", "longint");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 64u);

  v = FindVar(design, "m", "package");
  ASSERT_NE(v, nullptr);
  EXPECT_TRUE(v->is_event);
}

// The elaborated design keeps nets and constants in containers of their own,
// separate from the variables above, so a freed word has to survive each of
// those paths in its own right. This also puts both sides of the rule in one
// declaration list: the constants are introduced by `parameter`, inherited from
// the earlier list, and by `localparam`, an addition of this version, while
// every name they carry is a word a later standard reserved.
TEST(Verilog2001KeywordElaboration, FreedWordsNameElaboratedNetsAndConstants) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(In2001("module m;\n"
                                                  "  wire [7:0] string;\n"
                                                  "  wand       byte;\n"
                                                  "  parameter  int  = 8;\n"
                                                  "  localparam enum = 9;\n"
                                                  "endmodule\n"),
                                           f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* n = FindNet(design, "m", "string");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->width, 8u);
  EXPECT_EQ(n->net_type, NetType::kWire);

  n = FindNet(design, "m", "byte");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->net_type, NetType::kWand);

  const auto* p = FindParam(design, "m", "int");
  ASSERT_NE(p, nullptr);
  EXPECT_FALSE(p->is_localparam);
  EXPECT_EQ(p->resolved_value, 8);

  p = FindParam(design, "m", "enum");
  ASSERT_NE(p, nullptr);
  EXPECT_TRUE(p->is_localparam);
  EXPECT_EQ(p->resolved_value, 9);
}

// A freed word naming the design element itself, its ports, and the instance
// that binds to it -- the region governs a whole elaborated hierarchy, not one
// declaration inside one module.
TEST(Verilog2001KeywordElaboration, FreedWordNamesModulePortsAndInstance) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      In2001("module bit (input wire logic,\n"
             "            output wire byte);\n"
             "  assign byte = logic;\n"
             "endmodule\n"
             "module top;\n"
             "  wire a, b;\n"
             "  bit interface (.logic(a), .byte(b));\n"
             "endmodule\n"),
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* child = FindModule(design, "bit");
  ASSERT_NE(child, nullptr);
  ASSERT_EQ(child->ports.size(), 2u);
  EXPECT_EQ(child->ports[0].name, "logic");
  EXPECT_EQ(child->ports[0].direction, Direction::kInput);
  EXPECT_EQ(child->ports[1].name, "byte");
  EXPECT_EQ(child->ports[1].direction, Direction::kOutput);

  const auto* top = FindModule(design, "top");
  ASSERT_NE(top, nullptr);
  bool found_instance = false;
  for (const auto& inst : top->children) {
    if (inst.inst_name == "interface" && inst.module_name == "bit") {
      found_instance = true;
    }
  }
  EXPECT_TRUE(found_instance);
}

// The negative for the additions, carried to this stage: none of the words
// Table 22-2 lists can name a variable that reaches the design, while the same
// declaration under the list this version extends builds one. Sweeping all
// twenty-one rather than sampling is what makes the table, and not a handful of
// its entries, the thing being checked.
TEST(Verilog2001KeywordElaboration, AdditionsCannotNameElaboratedVariables) {
  for (const char* word : kTable222) {
    std::string decl =
        std::string("module t;\n  reg [7:0] ") + word + ";\nendmodule\n";

    ElabFixture reserved;
    ElaborateWithPreprocessor(In2001(decl), reserved, "t");
    EXPECT_TRUE(reserved.has_errors) << word;

    ElabFixture freed;
    auto* design = ElaborateWithPreprocessor(In1995(decl), freed, "t");
    ASSERT_NE(design, nullptr) << word;
    EXPECT_FALSE(freed.has_errors) << word;
    const auto* v = FindVar(design, "t", word);
    ASSERT_NE(v, nullptr) << word;
    EXPECT_EQ(v->width, 8u) << word;
  }
}

// The negative from the other direction: a word neither table lists carries no
// keyword meaning, so a declaration written with it as a data type does not
// elaborate. `uwire` is the sharpest case, being the sole word the very next
// version adds. The same source outside the region does elaborate, which is
// what shows the region -- and not some unrelated limitation -- is doing the
// rejecting.
TEST(Verilog2001KeywordElaboration, WordOutsideTheListIsNotADataType) {
  const char* kDecls[] = {"logic [7:0] v;", "uwire v;", "bit [7:0] v;"};
  for (const char* decl : kDecls) {
    ElabFixture in_region;
    ElaborateWithPreprocessor(
        In2001(std::string("module t;\n  ") + decl + "\nendmodule\n"),
        in_region, "t");
    EXPECT_TRUE(in_region.has_errors) << decl;

    ElabFixture outside;
    auto* design = ElaborateWithPreprocessor(
        std::string("module t;\n  ") + decl + "\nendmodule\n", outside, "t");
    ASSERT_NE(design, nullptr) << decl;
    EXPECT_FALSE(outside.has_errors) << decl;
  }
}

}  // namespace
