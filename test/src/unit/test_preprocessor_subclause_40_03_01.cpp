#include <gtest/gtest.h>

#include <cctype>
#include <cstddef>
#include <string>

#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

std::string ExpandMacro(const std::string& name) {
  PreprocFixture f;
  auto out = Preprocess("`" + name + "\n", f);
  EXPECT_FALSE(f.diag.HasErrors())
      << "unexpected diagnostics expanding " << name;
  size_t begin = 0;
  size_t end = out.size();
  while (begin < end && std::isspace(static_cast<unsigned char>(out[begin])))
    ++begin;
  while (end > begin && std::isspace(static_cast<unsigned char>(out[end - 1])))
    --end;
  return out.substr(begin, end - begin);
}

TEST(CoverageConstantsPreprocessor, CoverageControl) {
  EXPECT_EQ(ExpandMacro("SV_COV_START"), "0");
  EXPECT_EQ(ExpandMacro("SV_COV_STOP"), "1");
  EXPECT_EQ(ExpandMacro("SV_COV_RESET"), "2");
  EXPECT_EQ(ExpandMacro("SV_COV_CHECK"), "3");
}

TEST(CoverageConstantsPreprocessor, ScopeDefinition) {
  EXPECT_EQ(ExpandMacro("SV_COV_MODULE"), "10");
  EXPECT_EQ(ExpandMacro("SV_COV_HIER"), "11");
}

TEST(CoverageConstantsPreprocessor, CoverageTypeIdentification) {
  EXPECT_EQ(ExpandMacro("SV_COV_ASSERTION"), "20");
  EXPECT_EQ(ExpandMacro("SV_COV_FSM_STATE"), "21");
  EXPECT_EQ(ExpandMacro("SV_COV_STATEMENT"), "22");
  EXPECT_EQ(ExpandMacro("SV_COV_TOGGLE"), "23");
}

TEST(CoverageConstantsPreprocessor, StatusResults) {
  EXPECT_EQ(ExpandMacro("SV_COV_OVERFLOW"), "-2");
  EXPECT_EQ(ExpandMacro("SV_COV_ERROR"), "-1");
  EXPECT_EQ(ExpandMacro("SV_COV_NOCOV"), "0");
  EXPECT_EQ(ExpandMacro("SV_COV_OK"), "1");
  EXPECT_EQ(ExpandMacro("SV_COV_PARTIAL"), "2");
}

TEST(CoverageConstantsPreprocessor, UsableWithoutUserDefine) {
  PreprocFixture f;
  auto out = Preprocess(
      "module m;\n"
      "  localparam int c = `SV_COV_CHECK;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("localparam int c = 3"), std::string::npos);
}

TEST(CoverageConstantsPreprocessor, DefinedForConditionalCompilation) {
  PreprocFixture f;
  auto out = Preprocess(
      "`ifdef SV_COV_OK\n"
      "selected\n"
      "`else\n"
      "absent\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("selected"), std::string::npos);
  EXPECT_EQ(out.find("absent"), std::string::npos);
}

TEST(CoverageConstantsPreprocessor, UnlistedNameIsNotPredefined) {
  PreprocFixture f;
  Preprocess("`SV_COV_UNDEFINED\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "undefined macro 'SV_COV_UNDEFINED'", 1, "22.5.1"));
}

}  // namespace
