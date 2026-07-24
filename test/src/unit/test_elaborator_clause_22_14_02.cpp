#include <string>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// Wraps `body` in a real `begin_keywords "1364-1995" region, so the reserved
// word list Table 22-1 gives is the one in force while the design is built.
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

// Words Table 22-1 omits are ordinary identifiers under this list, and they
// stay ordinary identifiers all the way into the elaborated design: each one
// names a variable that really exists there, carrying the storage its
// declaration asked for. Getting past the parser is not enough — the design is
// what the rest of the tool works from.
TEST(Verilog1995KeywordElaboration, FreedWordsNameElaboratedVariables) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(In1995("module m;\n"
                                                  "  reg [63:0] logic;\n"
                                                  "  reg [7:0]  bit;\n"
                                                  "  integer    int;\n"
                                                  "  real       shortreal;\n"
                                                  "  time       longint;\n"
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
}

// A freed word naming the design element itself, its ports, and the instance
// that binds to it — the region governs a whole elaborated hierarchy, not one
// declaration inside one module.
TEST(Verilog1995KeywordElaboration, FreedWordNamesModulePortsAndInstance) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      In1995("module bit (input wire logic,\n"
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

// The membership side at this stage: the variable type keywords Table 22-1
// lists still declare their own storage under this list, each with the width
// and the real/vector distinction its own type implies.
TEST(Verilog1995KeywordElaboration, ReservedTypeKeywordsKeepTheirStorage) {
  struct Case {
    const char* decl;
    uint32_t width;
    bool is_real;
  };
  const Case kCases[] = {
      {"reg v;", 1, false},      {"reg [15:0] v;", 16, false},
      {"integer v;", 32, false}, {"time v;", 64, false},
      {"real v;", 64, true},     {"realtime v;", 64, true},
  };
  for (const auto& c : kCases) {
    ElabFixture f;
    auto* design = ElaborateWithPreprocessor(
        In1995(std::string("module t;\n  ") + c.decl + "\nendmodule\n"), f,
        "t");
    ASSERT_NE(design, nullptr) << c.decl;
    EXPECT_FALSE(f.has_errors) << c.decl;

    const auto* v = FindVar(design, "t", "v");
    ASSERT_NE(v, nullptr) << c.decl;
    EXPECT_EQ(v->width, c.width) << c.decl;
    EXPECT_EQ(v->is_real, c.is_real) << c.decl;
  }
}

// The net type keywords of Table 22-1, carried into the design: each still
// selects its own net type rather than degrading to a plain wire.
TEST(Verilog1995KeywordElaboration, ReservedNetKeywordsKeepTheirNetType) {
  struct Case {
    const char* decl;
    NetType type;
  };
  const Case kCases[] = {
      {"wand n;", NetType::kWand},       {"wor n;", NetType::kWor},
      {"triand n;", NetType::kTriand},   {"trior n;", NetType::kTrior},
      {"tri0 n;", NetType::kTri0},       {"tri1 n;", NetType::kTri1},
      {"trireg n;", NetType::kTrireg},   {"supply0 n;", NetType::kSupply0},
      {"supply1 n;", NetType::kSupply1}, {"tri n;", NetType::kTri},
  };
  for (const auto& c : kCases) {
    ElabFixture f;
    auto* design = ElaborateWithPreprocessor(
        In1995(std::string("module t;\n  ") + c.decl + "\nendmodule\n"), f,
        "t");
    ASSERT_NE(design, nullptr) << c.decl;
    EXPECT_FALSE(f.has_errors) << c.decl;

    const auto* n = FindNet(design, "t", "n");
    ASSERT_NE(n, nullptr) << c.decl;
    EXPECT_EQ(n->net_type, c.type) << c.decl;
  }
}

// `event` is a Table 22-1 keyword whose declaration produces a kind of storage
// none of the numeric types above does, and the name it introduces here is a
// word a later standard reserved. Both sides of the rule meet in one
// declaration, and the elaborated design has to hold an event under that name.
TEST(Verilog1995KeywordElaboration, FreedWordNamesAnEventVariable) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(In1995("module t;\n"
                                                  "  event logic;\n"
                                                  "endmodule\n"),
                                           f, "t");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* v = FindVar(design, "t", "logic");
  ASSERT_NE(v, nullptr);
  EXPECT_TRUE(v->is_event);
}

// A declaration's width can come from a literal or from a constant declared
// with the Table 22-1 `parameter` keyword, and the two reach the elaborator by
// different paths. Under this list both have to arrive at the same width — the
// parameter case additionally proving that `parameter` still declares a
// constant here, and that a parameter named with a word a later standard
// reserved is still usable as one.
TEST(Verilog1995KeywordElaboration, ConstantWidthFromLiteralAndFromParameter) {
  struct Case {
    const char* body;
    const char* var_name;
  };
  const Case kCases[] = {
      {"module t;\n  reg [7:0] v;\nendmodule\n", "v"},
      {"module t;\n  parameter P = 8;\n  reg [P-1:0] v;\nendmodule\n", "v"},
      {"module t;\n  parameter int = 8;\n  reg [int-1:0] byte;\nendmodule\n",
       "byte"},
  };
  for (const auto& c : kCases) {
    ElabFixture f;
    auto* design = ElaborateWithPreprocessor(In1995(c.body), f, "t");
    ASSERT_NE(design, nullptr) << c.body;
    EXPECT_FALSE(f.has_errors) << c.body;

    const auto* v = FindVar(design, "t", c.var_name);
    ASSERT_NE(v, nullptr) << c.body;
    EXPECT_EQ(v->width, 8u) << c.body;
  }
}

// The negative at this stage: a word Table 22-1 omits carries no keyword
// meaning, so a declaration written with it as a data type does not elaborate.
// The same source outside the region does, which is what shows the region — and
// not some unrelated limitation — is doing the rejecting.
TEST(Verilog1995KeywordElaboration, WordOutsideTheListIsNotADataType) {
  ElabFixture in_region;
  ElaborateWithPreprocessor(In1995("module t;\n"
                                   "  logic [7:0] v;\n"
                                   "endmodule\n"),
                            in_region, "t");
  EXPECT_TRUE(in_region.has_errors);

  ElabFixture outside;
  auto* design = ElaborateWithPreprocessor(
      "module t;\n"
      "  logic [7:0] v;\n"
      "endmodule\n",
      outside, "t");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(outside.has_errors);
  const auto* v = FindVar(design, "t", "v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 8u);
}

}  // namespace
