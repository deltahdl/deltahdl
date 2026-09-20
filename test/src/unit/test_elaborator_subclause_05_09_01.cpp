#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

TEST(LexicalConventionElaboration, StringWithNamedEscapeElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  initial $display(\"hello\\nworld\");\n"
             "endmodule\n"));
}

TEST(LexicalConventionElaboration, StringWithOctalEscapeElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  byte c;\n"
             "  initial c = \"\\101\";\n"
             "endmodule\n"));
}

// Table 5-1 makes an x_digit or a z_digit illegal in a `\ddd` or `\xdd`
// escape, so a design whose display argument holds one is rejected as a whole
// rather than printing the character and then the letter.
TEST(LexicalConventionElaboration,
     DisplayArgumentWithXDigitInHexEscapeIsRejected) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module t;\n"
      "  initial $display(\"\\x4x\");\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "hex escape", 2, "5.9.1"));
}

TEST(LexicalConventionElaboration,
     DisplayArgumentWithZDigitInOctalEscapeIsRejected) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module t;\n"
      "  initial $display(\"\\1z\");\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "octal escape", 2, "5.9.1"));
}

}  // namespace
