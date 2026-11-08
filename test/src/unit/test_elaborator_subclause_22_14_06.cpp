#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_included_keyword_elab.h"
#include "helpers_keyword_version.h"
#include "helpers_reported_error.h"
#include "helpers_reserved_keyword_elab.h"
#include "helpers_rtlir_lookup.h"
#include "model_keyword_table_sweeps.h"

using namespace delta;

namespace {
TEST(SystemVerilog2005KeywordElaboration, IncludedVerilog1995WordsAreReserved) {
  ExpectKeywordTableIsReserved("1800-2005", kVerilog1995KeywordSweep);
}

TEST(SystemVerilog2005KeywordElaboration, IncludedVerilog2001WordsAreReserved) {
  ExpectKeywordTableIsReserved("1800-2005", kVerilog2001AddedKeywordSweep);
}

TEST(SystemVerilog2005KeywordElaboration, IncludedVerilog2005WordIsReserved) {
  ExpectKeywordTableIsReserved("1800-2005", kVerilog2005AddedKeywordSweep);
  ExpectVerilog2005DeclarationsElaborate("1800-2005");
}

TEST(SystemVerilog2005KeywordElaboration, AddedWordsCannotNameVariables) {
  ExpectKeywordTableIsReserved("1800-2005",
                               kSystemVerilog2005AddedKeywordSweep);
}

TEST(SystemVerilog2005KeywordElaboration, AddedWordsDoTheirElaboratedJobs) {
  ExpectSystemVerilog2005DeclarationsElaborate("1800-2005");
}

TEST(SystemVerilog2005KeywordElaboration,
     AddedTypeWordsTypeEveryDeclarationForm) {
  ExpectEveryDeclarationFormElaborates("1800-2005");
}

TEST(SystemVerilog2005KeywordElaboration, AddedTypeWordsQualifyConstants) {
  const std::string kSrc =
      "module t;\n"
      "  parameter  int  P = 21;\n"
      "  localparam byte S = 8'd1;\n"
      "  logic [P-1:0] from_typed_parameter;\n"
      "  logic [S+6:0]  from_typed_localparam;\n"
      "endmodule\n";

  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(InSv2005(kSrc), f, "t");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* p = FindParam(design, "t", "P");
  ASSERT_NE(p, nullptr);
  EXPECT_FALSE(p->is_localparam);
  EXPECT_EQ(p->resolved_value, 21);

  const auto* s = FindParam(design, "t", "S");
  ASSERT_NE(s, nullptr);
  EXPECT_TRUE(s->is_localparam);
  EXPECT_EQ(s->resolved_value, 1);

  const auto* wide = FindVar(design, "t", "from_typed_parameter");
  ASSERT_NE(wide, nullptr);
  EXPECT_EQ(wide->width, 21u);
  const auto* narrow = FindVar(design, "t", "from_typed_localparam");
  ASSERT_NE(narrow, nullptr);
  EXPECT_EQ(narrow->width, 8u);

  ElabFixture included;
  ElaborateWithPreprocessorAllowingParseErrors(In2005(kSrc), included, "t");
  EXPECT_TRUE(ReportedError(included.diag.Diagnostics(),
                            "parameter declaration requires a default value",
                            LineInRegion(2), "6.20.1"));
}

TEST(SystemVerilog2005KeywordElaboration,
     IncludedVerilog1995WordsStillBuildDesign) {
  ExpectVerilog1995DeclarationsElaborate("1800-2005");
}

TEST(SystemVerilog2005KeywordElaboration,
     IncludedVerilog2001WordsStillBuildDesign) {
  ExpectVerilog2001DeclarationsElaborate("1800-2005");
}

TEST(SystemVerilog2005KeywordElaboration,
     EveryConstantFormResolvesUnderThisVersion) {
  ExpectEveryConstantFormResolves("1800-2005", "", "");
}

TEST(SystemVerilog2005KeywordElaboration,
     UnlistedWordsNameObjectsButAreNotTypes) {
  ExpectWordsNameObjectsButAreNotTypes(
      "1800-2005", {"until", "let", "global", "nettype", "soft"});
}

}  // namespace
