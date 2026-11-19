#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(SpecifyBlockDeclElaboration, ShowcancelledBeforeModulePathIsLegal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output o);\n"
      "  specify\n"
      "    showcancelled o;\n"
      "    (a => o) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyBlockDeclElaboration, ShowcancelledAfterModulePathIsError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output o);\n"
      "  specify\n"
      "    (a => o) = 5;\n"
      "    showcancelled o;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  (void)design;
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "showcancelled declaration for 'o' conflicts with a "
                    "module path that drives the same output",
                    4, "30.7.4.2"));
}

TEST(SpecifyBlockDeclElaboration,
     ConflictAmongMultipleShowcancelledOutputsIsError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output o, output p);\n"
      "  specify\n"
      "    (a => o) = 5;\n"
      "    showcancelled p, o;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  (void)design;
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "showcancelled declaration for 'o' conflicts with a "
                    "module path that drives the same output",
                    4, "30.7.4.2"));
}

TEST(SpecifyBlockDeclElaboration,
     ShowcancelledAfterAPathOfAnEarlierBlockIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input a, output o);\n"
      "  specify\n"
      "    (a => o) = 5;\n"
      "  endspecify\n"
      "  specify\n"
      "    showcancelled o;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "showcancelled declaration for 'o' conflicts with a "
                    "module path that drives the same output",
                    6, "30.7.4.2"));
}

TEST(SpecifyBlockDeclElaboration, NoshowcancelledAfterModulePathIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input a, output o);\n"
      "  specify\n"
      "    (a => o) = 5;\n"
      "    noshowcancelled o;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "noshowcancelled declaration for 'o' conflicts with a "
                    "module path that drives the same output",
                    4, "30.7.4.2"));
}

TEST(SpecifyBlockDeclElaboration, NoshowcancelledBeforeModulePathIsLegal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output o);\n"
      "  specify\n"
      "    noshowcancelled o;\n"
      "    (a => o) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyBlockDeclElaboration, ShowcancelledBetweenTwoPathsToOutputIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input a, input b, output out);\n"
      "  specify\n"
      "    (a => out) = (2, 3);\n"
      "    showcancelled out;\n"
      "    (b => out) = (3, 4);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "showcancelled declaration for 'out' conflicts with a "
                    "module path that drives the same output",
                    4, "30.7.4.2"));
}

TEST(SpecifyBlockDeclElaboration, ShowcancelledOnOtherOutputAfterPathsIsLegal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, input b, output out, output out_b);\n"
      "  specify\n"
      "    showcancelled out;\n"
      "    pulsestyle_ondetect out;\n"
      "    (a => out) = (2, 3);\n"
      "    (b => out) = (4, 5);\n"
      "    showcancelled out_b;\n"
      "    pulsestyle_ondetect out_b;\n"
      "    (a => out_b) = (3, 4);\n"
      "    (b => out_b) = (5, 6);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
