#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(SpecifyBlockDeclElaboration, PulsestyleOnModulePathOutputIsError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output o);\n"
      "  specify\n"
      "    (a => o) = 5;\n"
      "    pulsestyle_onevent o;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  (void)design;
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pulsestyle declaration for 'o' conflicts with a "
                            "module path that drives the same output",
                            4, "30.7.4.1"));
}

TEST(SpecifyBlockDeclElaboration, PulsestyleBeforeModulePathIsLegal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output o);\n"
      "  specify\n"
      "    pulsestyle_onevent o;\n"
      "    (a => o) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyBlockDeclElaboration,
     ConflictAmongMultiplePulsestyleOutputsIsError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output o, output p);\n"
      "  specify\n"
      "    (a => o) = 5;\n"
      "    pulsestyle_onevent p, o;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  (void)design;
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pulsestyle declaration for 'o' conflicts with a "
                            "module path that drives the same output",
                            4, "30.7.4.1"));
}

TEST(SpecifyBlockDeclElaboration, PulsestyleOndetectOnModulePathOutputIsError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output o);\n"
      "  specify\n"
      "    (a => o) = 5;\n"
      "    pulsestyle_ondetect o;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  (void)design;
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pulsestyle declaration for 'o' conflicts with a "
                            "module path that drives the same output",
                            4, "30.7.4.1"));
}

TEST(SpecifyBlockDeclElaboration, PulsestyleOndetectBeforeModulePathIsLegal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output o);\n"
      "  specify\n"
      "    pulsestyle_ondetect o;\n"
      "    (a => o) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyBlockDeclElaboration, PulsestyleInLaterSpecifyBlockIsError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output o);\n"
      "  specify\n"
      "    (a => o) = 5;\n"
      "  endspecify\n"
      "  specify\n"
      "    pulsestyle_ondetect o;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  (void)design;
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pulsestyle declaration for 'o' conflicts with a "
                            "module path that drives the same output",
                            6, "30.7.4.1"));
}

TEST(SpecifyBlockDeclElaboration, PulsestyleInEarlierSpecifyBlockIsLegal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output o);\n"
      "  specify\n"
      "    pulsestyle_ondetect o;\n"
      "  endspecify\n"
      "  specify\n"
      "    (a => o) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyBlockDeclElaboration, PulsestyleOnOtherOutputAfterPathsIsLegal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, input b, output out, output out_b);\n"
      "  specify\n"
      "    (a => out) = (2, 3);\n"
      "    (b => out) = (3, 4);\n"
      "    pulsestyle_ondetect out_b;\n"
      "    (a => out_b) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
