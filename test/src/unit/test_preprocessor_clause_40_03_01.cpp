#include <gtest/gtest.h>

#include <cctype>
#include <string>

#include "fixture_preprocessor.h"

using namespace delta;

namespace {

// §40.3.1 requires the listed coverage constants to be available as predefined
// text macros. Expanding a bare reference to one of them yields its value; the
// preprocessor surrounds expansions with layout, so compare on trimmed text.
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

// §40.3.1 — coverage control constants.
TEST(CoverageConstantsPreprocessor, CoverageControl) {
  EXPECT_EQ(ExpandMacro("SV_COV_START"), "0");
  EXPECT_EQ(ExpandMacro("SV_COV_STOP"), "1");
  EXPECT_EQ(ExpandMacro("SV_COV_RESET"), "2");
  EXPECT_EQ(ExpandMacro("SV_COV_CHECK"), "3");
}

// §40.3.1 — scope definition constants.
TEST(CoverageConstantsPreprocessor, ScopeDefinition) {
  EXPECT_EQ(ExpandMacro("SV_COV_MODULE"), "10");
  EXPECT_EQ(ExpandMacro("SV_COV_HIER"), "11");
}

// §40.3.1 — coverage type identification constants.
TEST(CoverageConstantsPreprocessor, CoverageTypeIdentification) {
  EXPECT_EQ(ExpandMacro("SV_COV_ASSERTION"), "20");
  EXPECT_EQ(ExpandMacro("SV_COV_FSM_STATE"), "21");
  EXPECT_EQ(ExpandMacro("SV_COV_STATEMENT"), "22");
  EXPECT_EQ(ExpandMacro("SV_COV_TOGGLE"), "23");
}

// §40.3.1 — status result constants, including the negative-valued ones.
TEST(CoverageConstantsPreprocessor, StatusResults) {
  EXPECT_EQ(ExpandMacro("SV_COV_OVERFLOW"), "-2");
  EXPECT_EQ(ExpandMacro("SV_COV_ERROR"), "-1");
  EXPECT_EQ(ExpandMacro("SV_COV_NOCOV"), "0");
  EXPECT_EQ(ExpandMacro("SV_COV_OK"), "1");
  EXPECT_EQ(ExpandMacro("SV_COV_PARTIAL"), "2");
}

// The constants are predefined, so they expand without any user `define and are
// usable directly in SystemVerilog source as §40.3.1 specifies.
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

// Being predefined `define macros, the constants must be visible to conditional
// compilation directives — proving they are real macro-table entries, not ad
// hoc textual substitutions. This exercises the `ifdef path rather than
// expansion.
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

// §40.3.1 fixes an exact, bounded set of predefined coverage constants. A name
// that merely follows the SV_COV_ family convention but is not on that list is
// therefore NOT predefined: referencing it is an undefined-macro error. This is
// the negative counterpart to the accepting cases above and confirms the
// predefinition is a specific macro-table membership, not a blanket rule that
// swallows any SV_COV_ identifier.
TEST(CoverageConstantsPreprocessor, UnlistedNameIsNotPredefined) {
  PreprocFixture f;
  Preprocess("`SV_COV_UNDEFINED\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
