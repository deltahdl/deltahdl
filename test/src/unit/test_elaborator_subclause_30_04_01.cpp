#include <gtest/gtest.h>

#include <string>

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

constexpr const char* kOutputSource =
    "module path source 'o' must be connected to an input or inout port";

bool TerminalReported(const std::string& ports, const std::string& path,
                      const std::string& message) {
  ElabFixture f;
  ElaborateSrc("module m(" + ports +
                   ");\n"
                   "  specify\n"
                   "    " +
                   path +
                   "\n"
                   "  endspecify\n"
                   "endmodule\n",
               f);
  return ReportedError(f.diag.Diagnostics(), message, 3, "30.4.1");
}

bool TerminalsAccepted(const std::string& ports, const std::string& path) {
  ElabFixture f;
  auto* design = ElaborateSrc("module m(" + ports +
                                  ");\n"
                                  "  specify\n"
                                  "    " +
                                  path +
                                  "\n"
                                  "  endspecify\n"
                                  "endmodule\n",
                              f);
  return design != nullptr && !f.has_errors;
}

TEST(SpecifyTerminalElaboration, OutputInAFullPathSourceListErrors) {
  EXPECT_TRUE(TerminalReported("input i, output o, output y",
                               "(i, o *> y) = 5;", kOutputSource));
}

TEST(SpecifyTerminalElaboration, InputsInAFullPathSourceListElaborate) {
  EXPECT_TRUE(
      TerminalsAccepted("input i, input j, output y", "(i, j *> y) = 5;"));
}

TEST(SpecifyTerminalElaboration, InputInAFullPathDestinationListErrors) {
  EXPECT_TRUE(TerminalReported("input i, input i2, output y",
                               "(i *> y, i2) = 5;",
                               "module path destination 'i2' must be "
                               "connected to an output or inout port"));
}

TEST(SpecifyTerminalElaboration, OutputsInAFullPathDestinationListElaborate) {
  EXPECT_TRUE(
      TerminalsAccepted("input i, output y, output z", "(i *> y, z) = 5;"));
}

TEST(SpecifyTerminalElaboration, OutputAsEdgeSensitivePathSourceErrors) {
  EXPECT_TRUE(TerminalReported("input i, output o, output y",
                               "(posedge o => (y : i)) = 5;", kOutputSource));
}

TEST(SpecifyTerminalElaboration, InputAsEdgeSensitivePathDestinationErrors) {
  EXPECT_TRUE(TerminalReported("input i, input c, output y",
                               "(posedge c => (i : c)) = 5;",
                               "module path destination 'i' must be "
                               "connected to an output or inout port"));
}

TEST(SpecifyTerminalElaboration, EdgeSensitivePathOnPortsElaborates) {
  EXPECT_TRUE(TerminalsAccepted("input i, input c, output y",
                                "(posedge c => (y : i)) = 5;"));
}

TEST(SpecifyTerminalElaboration, OutputAsStateDependentPathSourceErrors) {
  EXPECT_TRUE(TerminalReported("input i, output o, output y",
                               "if (i) (o => y) = 5;", kOutputSource));
}

TEST(SpecifyTerminalElaboration, InputAsStateDependentPathDestinationErrors) {
  EXPECT_TRUE(TerminalReported("input i, input c, output y",
                               "if (i) (i => c) = 5;",
                               "module path destination 'c' must be "
                               "connected to an output or inout port"));
}

TEST(SpecifyTerminalElaboration, StateDependentPathOnPortsElaborates) {
  EXPECT_TRUE(
      TerminalsAccepted("input i, input c, output y", "if (i) (c => y) = 5;"));
}

TEST(SpecifyTerminalElaboration, SelectsOfVectorPortsElaborate) {
  EXPECT_TRUE(TerminalsAccepted("input [3:0] a, output [3:0] y",
                                "(a[0] => y[1]) = 5; (a[3:2] *> y[1:0]) = 4;"));
}

TEST(SpecifyTerminalElaboration, SelectOfAnOutputAsSourceErrors) {
  EXPECT_TRUE(TerminalReported(
      "input [3:0] a, output [3:0] y", "(y[0] => a[1]) = 5;",
      "module path source 'y' must be connected to an input or inout port"));
}

TEST(SpecifyTerminalElaboration, SelectOfAVariableInputAsSourceErrors) {
  EXPECT_TRUE(TerminalReported("input var logic [1:0] i, output o",
                               "(i[0] => o) = 5;",
                               "module path source 'i' must be a net"));
}

TEST(SpecifyTerminalElaboration, AnsiInputWithADataTypeIsANetSource) {
  EXPECT_TRUE(TerminalsAccepted("input logic i, output o", "(i => o) = 5;"));
}

TEST(SpecifyTerminalElaboration, ResolvedNetTypesAreTerminals) {
  EXPECT_TRUE(
      TerminalsAccepted("input tri1 i, output wand o", "(i => o) = 5;"));
}

TEST(SpecifyTerminalElaboration, LogicOutputVariableAsDestinationElaborates) {
  EXPECT_TRUE(TerminalsAccepted("input i, output logic o", "(i => o) = 5;"));
}

TEST(SpecifyTerminalElaboration, IntOutputVariableAsDestinationElaborates) {
  EXPECT_TRUE(TerminalsAccepted("input i, output int o", "(i *> o) = 5;"));
}

}  // namespace
