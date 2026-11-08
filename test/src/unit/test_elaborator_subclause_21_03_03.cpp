#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(StringFormatTaskElaboration, SwriteStringOutputVarAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string s;\n"
      "  initial $swrite(s, \"x=%0d\", 7);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StringFormatTaskElaboration, SwriteIntegralOutputVarAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] v;\n"
      "  initial $swrite(v, \"%h\", 8'hab);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StringFormatTaskElaboration, SwriteUnpackedByteArrayOutputVarAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  byte b [0:3];\n"
      "  initial $swrite(b, \"ABCD\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StringFormatTaskElaboration, SwriteRealOutputVarRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real r;\n"
      "  initial $swrite(r, \"x=%0d\", 7);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "$swrite/$sformat cannot write its text into a real "
                    "variable; give it an integral, string or "
                    "unpacked byte array target",
                    3, "21.3.3"));
}

TEST(StringFormatTaskElaboration, SformatRealOutputVarRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real r;\n"
      "  initial $sformat(r, \"v=%0d\", 3);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "$swrite/$sformat cannot write its text into a real "
                    "variable; give it an integral, string or "
                    "unpacked byte array target",
                    3, "21.3.3"));
}

TEST(StringFormatTaskElaboration, SformatfHasNoOutputVarCheck) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string s;\n"
      "  initial s = $sformatf(\"val=%0d\", 42);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StringFormatTaskElaboration,
     SwriteRealOutputVarInAnAssertionPassStatementRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real acc;\n"
      "  logic ready;\n"
      "  initial assert (ready) $swrite(acc, \"n=%0d\", 1);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$swrite/$sformat cannot write its text into a real", 4, "21.3.3"));
}

TEST(StringFormatTaskElaboration,
     SformatRealOutputVarInAnAssertionFailStatementRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real tally;\n"
      "  logic done;\n"
      "  initial assert (done) else $sformat(tally, \"t=%0d\", 2);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$swrite/$sformat cannot write its text into a real", 4, "21.3.3"));
}

TEST(StringFormatTaskElaboration, SwritebRealOutputVarInARandcaseItemRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real gauge;\n"
      "  initial randcase 3: $swriteb(gauge, \"%b\", 4'b1010); endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$swrite/$sformat cannot write its text into a real", 3, "21.3.3"));
}

TEST(StringFormatTaskElaboration,
     SwritehRealOutputVarInARandsequenceCodeBlockRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real level;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { $swriteh(level, \"%h\", 8'hab); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$swrite/$sformat cannot write its text into a real", 5, "21.3.3"));
}

}  // namespace
