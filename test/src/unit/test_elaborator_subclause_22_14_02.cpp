#include <string>

#include "fixture_elaborator.h"
#include "helpers_keyword_version.h"
#include "helpers_reported_error.h"
#include "helpers_reserved_keyword_elab.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

// Words Table 22-1 omits are ordinary identifiers under this list, and they
// stay ordinary identifiers all the way into the elaborated design: each one
// names a variable that really exists there, carrying the storage its
// declaration asked for. Getting past the parser is not enough — the design is
// what the rest of the tool works from.
TEST(Verilog1995KeywordElaboration, FreedWordsNameElaboratedVariables) {
  ExpectFreedWordsNameElaboratedVariables("1364-1995");
}

// A freed word naming the design element itself, its ports, and the instance
// that binds to it — the region governs a whole elaborated hierarchy, not one
// declaration inside one module.
TEST(Verilog1995KeywordElaboration, FreedWordNamesModulePortsAndInstance) {
  ExpectFreedWordsNameModulePortsAndInstance(
      "1364-1995", {"bit", "logic", "byte", "interface"});
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
  // `logic` is an ordinary identifier under 1364-1995, so the declaration is
  // read as one name followed by another and Parser::ParsePlainVarDecl in
  // src/parser/parser_items.cpp reports. The rejection this case rests on is
  // the parser's, which is why the source is not required to parse.
  ElaborateWithPreprocessorAllowingParseErrors(In1995("module t;\n"
                                                      "  logic [7:0] v;\n"
                                                      "endmodule\n"),
                                               in_region, "t");
  EXPECT_TRUE(ReportedError(in_region.diag.Diagnostics(),
                            "expected ';', got '['", LineInRegion(2), "6.8"));

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
