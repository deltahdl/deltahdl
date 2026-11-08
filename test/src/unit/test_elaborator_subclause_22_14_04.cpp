#include <gtest/gtest.h>

#include <iterator>
#include <string>

#include "common/types.h"
#include "fixture_elaborator.h"
#include "helpers_included_keyword_elab.h"
#include "helpers_keyword_version.h"
#include "helpers_reported_error.h"
#include "helpers_reserved_keyword_elab.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

constexpr const char* kExcluded[] = {
    "cell",    "config",   "design",  "endconfig", "incdir",
    "include", "instance", "liblist", "library",   "use",
};

constexpr const char* kKept[] = {
    "automatic",
    "endgenerate",
    "generate",
    "genvar",
    "localparam",
    "noshowcancelled",
    "pulsestyle_ondetect",
    "pulsestyle_onevent",
    "showcancelled",
    "signed",
    "unsigned",
};

TEST(NoconfigKeywordElaboration, ExcludedWordsNameElaboratedVariables) {
  EXPECT_EQ(std::size(kExcluded), 10u);
  for (const char* word : kExcluded) {
    std::string decl =
        std::string("module t;\n  reg [7:0] ") + word + ";\nendmodule\n";

    ElabFixture freed;
    auto* design = ElaborateWithPreprocessor(InNoconfig(decl), freed, "t");
    ASSERT_NE(design, nullptr) << word;
    EXPECT_FALSE(freed.has_errors) << word;
    const auto* v = FindVar(design, "t", word);
    ASSERT_NE(v, nullptr) << word;
    EXPECT_EQ(v->width, 8u) << word;

    ElabFixture reserved;
    ElaborateWithPreprocessorAllowingParseErrors(In2001(decl), reserved, "t");
    EXPECT_TRUE(
        ReportedError(reserved.diag.Diagnostics(),
                      std::string("expected identifier, got '") + word + "'",
                      LineInRegion(2), "6.8"))
        << word;
  }
}

TEST(NoconfigKeywordElaboration, KeptAdditionsCannotNameElaboratedVariables) {
  EXPECT_EQ(std::size(kKept), 11u);
  for (const char* word : kKept) {
    std::string decl =
        std::string("module t;\n  reg [7:0] ") + word + ";\nendmodule\n";

    ElabFixture reserved;
    ElaborateWithPreprocessorAllowingParseErrors(InNoconfig(decl), reserved,
                                                 "t");
    EXPECT_TRUE(
        ReportedError(reserved.diag.Diagnostics(),
                      std::string("expected identifier, got '") + word + "'",
                      LineInRegion(2), "6.8"))
        << word;

    ElabFixture freed;
    auto* design = ElaborateWithPreprocessor(In1995(decl), freed, "t");
    ASSERT_NE(design, nullptr) << word;
    EXPECT_FALSE(freed.has_errors) << word;
    const auto* v = FindVar(design, "t", word);
    ASSERT_NE(v, nullptr) << word;
    EXPECT_EQ(v->width, 8u) << word;
  }
}

TEST(NoconfigKeywordElaboration, ExcludedWordsNameElaboratedNetsAndConstants) {
  ElabFixture f;
  auto* design =
      ElaborateWithPreprocessor(InNoconfig("module m;\n"
                                           "  wire [7:0] library;\n"
                                           "  wand       liblist;\n"
                                           "  parameter  incdir = 8;\n"
                                           "  localparam include = 9;\n"
                                           "endmodule\n"),
                                f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* n = FindNet(design, "m", "library");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->width, 8u);
  EXPECT_EQ(n->net_type, NetType::kWire);

  n = FindNet(design, "m", "liblist");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->net_type, NetType::kWand);

  const auto* p = FindParam(design, "m", "incdir");
  ASSERT_NE(p, nullptr);
  EXPECT_FALSE(p->is_localparam);
  EXPECT_EQ(p->resolved_value, 8);

  p = FindParam(design, "m", "include");
  ASSERT_NE(p, nullptr);
  EXPECT_TRUE(p->is_localparam);
  EXPECT_EQ(p->resolved_value, 9);
}

TEST(NoconfigKeywordElaboration, ExcludedWordsNameEveryVariableKind) {
  ElabFixture f;
  auto* design =
      ElaborateWithPreprocessor(InNoconfig("module m;\n"
                                           "  reg [63:0] cell;\n"
                                           "  integer    config;\n"
                                           "  real       design;\n"
                                           "  time       endconfig;\n"
                                           "  event      use;\n"
                                           "endmodule\n"),
                                f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* v = FindVar(design, "m", "cell");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 64u);

  v = FindVar(design, "m", "config");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 32u);

  v = FindVar(design, "m", "design");
  ASSERT_NE(v, nullptr);
  EXPECT_TRUE(v->is_real);

  v = FindVar(design, "m", "endconfig");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 64u);

  v = FindVar(design, "m", "use");
  ASSERT_NE(v, nullptr);
  EXPECT_TRUE(v->is_event);
}

TEST(NoconfigKeywordElaboration, ExcludedWordNamesModulePortsAndInstance) {
  ExpectFreedWordsNameModulePortsAndInstance(
      "1364-2001-noconfig", {"cell", "design", "library", "config"});
}

TEST(NoconfigKeywordElaboration, KeptAdditionsStillBuildTheDesign) {
  ExpectVerilog2001DeclarationsElaborate("1364-2001-noconfig");
}

TEST(NoconfigKeywordElaboration, ExcludedWordsCarryConstantsThatSizeADecl) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      InNoconfig("module t;\n"
                 "  parameter  incdir  = 8;\n"
                 "  localparam liblist = 8;\n"
                 "  function automatic integer use(input reg [7:0] n);\n"
                 "    use = n;\n"
                 "  endfunction\n"
                 "  reg [7:0]           from_literal;\n"
                 "  reg [incdir-1:0]    from_parameter;\n"
                 "  reg [liblist-1:0]   from_localparam;\n"
                 "  reg [use(8)-1:0]    from_function;\n"
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

TEST(NoconfigKeywordElaboration, ExcludedWordNamesAGenvarDrivingAGenerateLoop) {
  ElabFixture f;
  auto* built = ElaborateWithPreprocessor(
      InNoconfig("module t;\n"
                 "  localparam incdir = 4;\n"
                 "  genvar design;\n"
                 "  generate\n"
                 "    for (design = 0; design < incdir; design = design + 1)\n"
                 "      begin : blk\n"
                 "        reg [7:0] slot;\n"
                 "        if (design == 1) begin : only_one\n"
                 "          reg [7:0] picked;\n"
                 "        end\n"
                 "      end\n"
                 "  endgenerate\n"
                 "endmodule\n"),
      f, "t");
  ASSERT_NE(built, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* bound = FindParam(built, "t", "incdir");
  ASSERT_NE(bound, nullptr);
  EXPECT_TRUE(bound->is_localparam);
  EXPECT_EQ(bound->resolved_value, 4);

  EXPECT_EQ(CountVarsEndingIn(built, "t", "slot"), 4u);
  EXPECT_EQ(CountVarsEndingIn(built, "t", "picked"), 1u);

  ElabFixture reserved;
  ElaborateWithPreprocessorAllowingParseErrors(
      In2001("module t;\n"
             "  localparam incdir = 4;\n"
             "  genvar design;\n"
             "endmodule\n"),
      reserved, "t");
  EXPECT_TRUE(ReportedError(reserved.diag.Diagnostics(),
                            "expected identifier, got 'incdir'",
                            LineInRegion(2), "6.20.1"));
}

TEST(NoconfigKeywordElaboration, WordOutsideTheListIsNotADataType) {
  ExpectDeclsFailInRegionButElaborateOutside(
      "1364-2001-noconfig", {"logic [7:0] v;", "uwire v;", "bit [7:0] v;"});
}

}  // namespace
