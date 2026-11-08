#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(SpecifyTerminalElaboration, InputPortAsSourceElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input i, output o);\n"
      "  specify\n"
      "    (i => o) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyTerminalElaboration, InoutPortAsInputTerminalElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(inout io, output o);\n"
      "  specify\n"
      "    (io => o) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyTerminalElaboration, InoutPortAsOutputTerminalElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input i, inout io);\n"
      "  specify\n"
      "    (i => io) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyTerminalElaboration, VariableAsDestinationElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input i, output reg o);\n"
      "  specify\n"
      "    (i => o) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyTerminalElaboration, OutputPortAsSourceErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input i, output o);\n"
      "  specify\n"
      "    (o => i) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "module path source 'o' must be connected to an input or inout port", 3,
      "30.4.1"));
}

TEST(SpecifyTerminalElaboration, InputPortAsDestinationErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input i1, input i2);\n"
      "  specify\n"
      "    (i1 => i2) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "module path destination 'i2' must be connected to "
                            "an output or inout port",
                            3, "30.4.1"));
}

TEST(SpecifyTerminalElaboration, RefPortAsTerminalErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m(ref logic r, output o);\n"
      "  specify\n"
      "    (r => o) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "ref port 'r' cannot be used as a terminal in a specify block", 3,
      "25.6"));
}

TEST(SpecifyTerminalElaboration, RefPortAsDestinationErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input i, ref logic r);\n"
      "  specify\n"
      "    (i => r) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "ref port 'r' cannot be used as a terminal in a specify block", 3,
      "25.6"));
}

TEST(SpecifyTerminalElaboration, UnconnectedSourceErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m(output o);\n"
      "  wire local_net;\n"
      "  specify\n"
      "    (local_net => o) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "module path source 'local_net' is not connected "
                            "to an input or inout port",
                            4, "30.4.1"));
}

TEST(SpecifyTerminalElaboration, UnconnectedDestinationErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input i);\n"
      "  wire local_net;\n"
      "  specify\n"
      "    (i => local_net) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "module path destination 'local_net' is not "
                            "connected to an output or inout port",
                            4, "30.4.1"));
}

TEST(SpecifyTerminalElaboration, VariableAsSourceErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input var logic i, output o);\n"
      "  specify\n"
      "    (i => o) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "module path source 'i' must be a net", 3,
                            "30.4.1"));
}

TEST(SpecifyTerminalElaboration, VariableSourceNames30_4_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input var logic i, output o);\n"
      "  specify\n"
      "    (i => o) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "must be a net", 3, "30.4.1"));
}

TEST(SpecifyTerminalElaboration, NonAnsiInputWithNoTypeIsANetSource) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module mybuf(q, a);\n"
      "  output q;\n"
      "  input a;\n"
      "  assign q = a;\n"
      "  specify\n"
      "    (a => q) = (6, 8);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyTerminalElaboration, NonAnsiInputRedeclaredAsAVariable) {
  ElabFixture f;
  ElaborateSrc(
      "module mybuf(q, a);\n"
      "  output q;\n"
      "  input a;\n"
      "  reg a;\n"
      "  assign q = a;\n"
      "  specify\n"
      "    (a => q) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "module path source 'a' must be a net", 7,
                            "30.4.1"));
}

}  // namespace
