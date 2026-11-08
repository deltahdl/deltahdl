#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(MultiplePathDeclarationElaboration, MixedWidthsInBothLists) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, input [3:0] b, input [7:0] c,\n"
      "         output x, output [15:0] y);\n"
      "  specify\n"
      "    (a, b, c *> x, y) = 4;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(MultiplePathDeclarationElaboration, EveryDestinationInListIsAnEndpoint) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input a, input b, output x, input y);\n"
      "  specify\n"
      "    (a, b *> x, y) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "module path destination 'y' must be connected to an output", 3,
      "30.4.1"));
}

TEST(MultiplePathDeclarationElaboration, EverySourceInListIsAnEndpoint) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input a, output b, output x, output y);\n"
      "  specify\n"
      "    (a, b *> x, y) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "module path source 'b' must be connected to an input", 3, "30.4.1"));
}

TEST(MultiplePathDeclarationElaboration,
     ScalarSourceToVectorDestinationAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, input b, output [7:0] x, output [3:0] y);\n"
      "  specify\n"
      "    (a, b *> x, y) = 3;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(MultiplePathDeclarationElaboration,
     VectorSourceToScalarDestinationAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input [7:0] a, input [3:0] b, output x, output y);\n"
      "  specify\n"
      "    (a, b *> x, y) = 3;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(MultiplePathDeclarationElaboration,
     UnequalVectorWidthsAcrossListsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input [7:0] a, input [1:0] b,\n"
      "         output [3:0] x, output [15:0] y);\n"
      "  specify\n"
      "    (a, b *> x, y) = 3;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
