#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/types.h"
#include "fixture_elaborator.h"
#include "helpers_keyword_version.h"
#include "helpers_reported_error.h"
#include "helpers_reserved_keyword_elab.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

TEST(Verilog1995KeywordElaboration, FreedWordsNameElaboratedVariables) {
  ExpectFreedWordsNameElaboratedVariables("1364-1995");
}

TEST(Verilog1995KeywordElaboration, FreedWordNamesModulePortsAndInstance) {
  ExpectFreedWordsNameModulePortsAndInstance(
      "1364-1995", {"bit", "logic", "byte", "interface"});
}

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

TEST(Verilog1995KeywordElaboration, WordOutsideTheListIsNotADataType) {
  ElabFixture in_region;
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
