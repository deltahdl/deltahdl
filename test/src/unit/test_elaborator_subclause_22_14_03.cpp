#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/types.h"
#include "fixture_elaborator.h"
#include "helpers_included_keyword_elab.h"
#include "helpers_keyword_version.h"
#include "helpers_reserved_keyword_elab.h"
#include "helpers_rtlir_lookup.h"
#include "model_keyword_table_sweeps.h"

using namespace delta;

namespace {

TEST(Verilog2001KeywordElaboration, AdditionsDoTheirElaboratedJob) {
  ExpectVerilog2001DeclarationsElaborate("1364-2001");
}

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

  const char* const kNames[] = {"from_literal", "from_parameter",
                                "from_localparam", "from_function"};
  for (const char* name : kNames) {
    const auto* v = FindVar(design, "t", name);
    ASSERT_NE(v, nullptr) << name;
    EXPECT_EQ(v->width, 8u) << name;
  }
}

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

TEST(Verilog2001KeywordElaboration, FreedWordsNameElaboratedVariables) {
  ExpectFreedWordsNameElaboratedVariables("1364-2001");
}

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

TEST(Verilog2001KeywordElaboration, FreedWordNamesModulePortsAndInstance) {
  ExpectFreedWordsNameModulePortsAndInstance(
      "1364-2001", {"bit", "logic", "byte", "interface"});
}

TEST(Verilog2001KeywordElaboration, AdditionsCannotNameElaboratedVariables) {
  ExpectKeywordTableIsReserved("1364-2001", kVerilog2001AddedKeywordSweep);
}

TEST(Verilog2001KeywordElaboration, WordOutsideTheListIsNotADataType) {
  ExpectDeclsFailInRegionButElaborateOutside(
      "1364-2001", {"logic [7:0] v;", "uwire v;", "bit [7:0] v;"});
}

}  // namespace
