#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr const char* kAlways = "always procedures not allowed in programs";
constexpr const char* kPrimitive =
    "primitive instances not allowed in programs";
constexpr const char* kInst = "instantiations not allowed in programs";

::testing::AssertionResult ReportedAlone(const std::string& src,
                                         std::string_view message,
                                         uint32_t line) {
  auto r = Parse(src);
  auto found = ReportedError(r.diags, message, line, "24.3");
  if (!found) return found;
  auto errors = std::count_if(r.diags.begin(), r.diags.end(), [](auto& d) {
    return d.severity == DiagSeverity::kError;
  });
  if (errors != 1) {
    return ::testing::AssertionFailure()
           << errors << " errors were reported, where only the one at line "
           << line << " belongs";
  }
  return ::testing::AssertionSuccess();
}

TEST(ProgramExclusion, AnAlwaysInAnIfGenerateBlockIsReported) {
  EXPECT_TRUE(
      ReportedAlone("program p;\n"
                    "  logic clk, d, q;\n"
                    "  if (1) begin : g\n"
                    "    always @(posedge clk) q <= d;\n"
                    "  end\n"
                    "endprogram\n",
                    kAlways, 4));
}

TEST(ProgramExclusion, AnAlwaysInACaseGenerateBlockIsReported) {
  EXPECT_TRUE(
      ReportedAlone("program p;\n"
                    "  logic clk, d, q;\n"
                    "  case (1)\n"
                    "    1: begin : g\n"
                    "      always @(posedge clk) q <= d;\n"
                    "    end\n"
                    "  endcase\n"
                    "endprogram\n",
                    kAlways, 5));
}

TEST(ProgramExclusion, AnAlwaysFfInALoopGenerateBlockIsReported) {
  EXPECT_TRUE(
      ReportedAlone("program p;\n"
                    "  logic clk, d, q;\n"
                    "  for (genvar i = 0; i < 2; i++) begin : g\n"
                    "    always_ff @(posedge clk) q <= d;\n"
                    "  end\n"
                    "endprogram\n",
                    kAlways, 4));
}

TEST(ProgramExclusion, AnAlwaysInAProgramNestedInAModuleIsReported) {
  EXPECT_TRUE(
      ReportedAlone("module m;\n"
                    "  logic clk, d, q;\n"
                    "  program p;\n"
                    "    always @(posedge clk) q <= d;\n"
                    "  endprogram\n"
                    "endmodule\n",
                    kAlways, 4));
}

TEST(ProgramExclusion, AnAlwaysCombInAProgramNestedInAnInterfaceIsReported) {
  EXPECT_TRUE(
      ReportedAlone("interface i;\n"
                    "  logic a, b;\n"
                    "  program p;\n"
                    "    always_comb b = a;\n"
                    "  endprogram\n"
                    "endinterface\n",
                    kAlways, 4));
}

TEST(ProgramExclusion, AnAlwaysInTheModuleAroundANestedProgramIsAccepted) {
  auto r = Parse(
      "module m;\n"
      "  logic clk, d, q;\n"
      "  always @(posedge clk) q <= d;\n"
      "  program p;\n"
      "    initial q = 0;\n"
      "  endprogram\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ProgramExclusion, AnNOutputGateIsReported) {
  EXPECT_TRUE(
      ReportedAlone("program p;\n"
                    "  wire a, y;\n"
                    "  not g(y, a);\n"
                    "endprogram\n",
                    kPrimitive, 3));
}

TEST(ProgramExclusion, AnEnableGateIsReported) {
  EXPECT_TRUE(
      ReportedAlone("program p;\n"
                    "  wire a, en, y;\n"
                    "  bufif1 g(y, a, en);\n"
                    "endprogram\n",
                    kPrimitive, 3));
}

TEST(ProgramExclusion, AMosSwitchIsReported) {
  EXPECT_TRUE(
      ReportedAlone("program p;\n"
                    "  wire a, c, y;\n"
                    "  nmos g(y, a, c);\n"
                    "endprogram\n",
                    kPrimitive, 3));
}

TEST(ProgramExclusion, ACmosSwitchIsReported) {
  EXPECT_TRUE(
      ReportedAlone("program p;\n"
                    "  wire a, n, pc, y;\n"
                    "  cmos g(y, a, n, pc);\n"
                    "endprogram\n",
                    kPrimitive, 3));
}

TEST(ProgramExclusion, ABidirectionalPassSwitchIsReported) {
  EXPECT_TRUE(
      ReportedAlone("program p;\n"
                    "  wire a, b;\n"
                    "  tran g(a, b);\n"
                    "endprogram\n",
                    kPrimitive, 3));
}

TEST(ProgramExclusion, AnEnabledPassSwitchIsReported) {
  EXPECT_TRUE(
      ReportedAlone("program p;\n"
                    "  wire a, b, en;\n"
                    "  tranif1 g(a, b, en);\n"
                    "endprogram\n",
                    kPrimitive, 3));
}

TEST(ProgramExclusion, AnUnnamedPullSourceIsReported) {
  EXPECT_TRUE(
      ReportedAlone("program p;\n"
                    "  wire a;\n"
                    "  pullup (a);\n"
                    "endprogram\n",
                    kPrimitive, 3));
}

TEST(ProgramExclusion, AnEarlierUdpInAnIfGenerateBlockIsReported) {
  EXPECT_TRUE(
      ReportedAlone("primitive inv(output o, input i);\n"
                    "  table 0 : 1; 1 : 0; endtable\n"
                    "endprimitive\n"
                    "program p;\n"
                    "  wire a, b;\n"
                    "  if (1) begin : g\n"
                    "    inv u1(a, b);\n"
                    "  end\n"
                    "endprogram\n",
                    kPrimitive, 7));
}

TEST(ProgramExclusion, AGateInAnIfGenerateBlockIsReported) {
  EXPECT_TRUE(
      ReportedAlone("program p;\n"
                    "  wire a, b, c;\n"
                    "  if (1) begin : g\n"
                    "    and g1(c, a, b);\n"
                    "  end\n"
                    "endprogram\n",
                    kPrimitive, 4));
}

TEST(ProgramExclusion, AGateInAProgramNestedInAModuleIsReported) {
  EXPECT_TRUE(
      ReportedAlone("module m;\n"
                    "  program p;\n"
                    "    wire a, b, c;\n"
                    "    and g1(c, a, b);\n"
                    "  endprogram\n"
                    "endmodule\n",
                    kPrimitive, 4));
}

TEST(ProgramExclusion, AGateInTheModuleAroundANestedProgramIsAccepted) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, c;\n"
      "  and g1(c, a, b);\n"
      "  program p;\n"
      "  endprogram\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ProgramExclusion, AModuleInstanceInALoopGenerateBlockIsReported) {
  EXPECT_TRUE(
      ReportedAlone("module sub; endmodule\n"
                    "program p;\n"
                    "  for (genvar i = 0; i < 2; i++) begin : g\n"
                    "    sub u();\n"
                    "  end\n"
                    "endprogram\n",
                    kInst, 4));
}

TEST(ProgramExclusion, AModuleInstanceWithAParameterValueIsReported) {
  EXPECT_TRUE(
      ReportedAlone("module sub #(parameter int W = 1); endmodule\n"
                    "program p;\n"
                    "  sub #(2) u0();\n"
                    "endprogram\n",
                    kInst, 3));
}

TEST(ProgramExclusion, AModuleInstanceInAProgramNestedInAModuleIsReported) {
  EXPECT_TRUE(
      ReportedAlone("module sub; endmodule\n"
                    "module m;\n"
                    "  program p;\n"
                    "    sub u0();\n"
                    "  endprogram\n"
                    "endmodule\n",
                    kInst, 4));
}

TEST(ProgramExclusion, AModuleInstanceAroundANestedProgramIsAccepted) {
  auto r = Parse(
      "module sub; endmodule\n"
      "module m;\n"
      "  sub u0();\n"
      "  program p;\n"
      "  endprogram\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ProgramExclusion, AnInterfaceInstanceInALoopGenerateBlockIsReported) {
  EXPECT_TRUE(
      ReportedAlone("interface bus; endinterface\n"
                    "program p;\n"
                    "  for (genvar i = 0; i < 2; i++) begin : g\n"
                    "    bus inst();\n"
                    "  end\n"
                    "endprogram\n",
                    kInst, 4));
}

TEST(ProgramExclusion, AnInterfaceInstanceInAnIfGenerateBlockIsReported) {
  EXPECT_TRUE(
      ReportedAlone("interface bus; endinterface\n"
                    "program p;\n"
                    "  if (1) begin : g\n"
                    "    bus inst();\n"
                    "  end\n"
                    "endprogram\n",
                    kInst, 4));
}

TEST(ProgramExclusion, AnInterfaceInstanceInANestedProgramIsReported) {
  EXPECT_TRUE(
      ReportedAlone("interface bus; endinterface\n"
                    "module m;\n"
                    "  program p;\n"
                    "    bus inst();\n"
                    "  endprogram\n"
                    "endmodule\n",
                    kInst, 4));
}

TEST(ProgramExclusion, AProgramInstanceInALoopGenerateBlockIsReported) {
  EXPECT_TRUE(
      ReportedAlone("program other; endprogram\n"
                    "program p;\n"
                    "  for (genvar i = 0; i < 2; i++) begin : g\n"
                    "    other inst();\n"
                    "  end\n"
                    "endprogram\n",
                    kInst, 4));
}

TEST(ProgramExclusion, AProgramInstanceInAnIfGenerateBlockIsReported) {
  EXPECT_TRUE(
      ReportedAlone("program other; endprogram\n"
                    "program p;\n"
                    "  if (1) begin : g\n"
                    "    other inst();\n"
                    "  end\n"
                    "endprogram\n",
                    kInst, 4));
}

TEST(ProgramExclusion, AProgramInstanceInANestedProgramIsReported) {
  EXPECT_TRUE(
      ReportedAlone("program other; endprogram\n"
                    "module m;\n"
                    "  program p;\n"
                    "    other inst();\n"
                    "  endprogram\n"
                    "endmodule\n",
                    kInst, 4));
}

TEST(ProgramExclusion, AProgramInstanceInTheModuleAroundItIsAccepted) {
  auto r = Parse(
      "program other; endprogram\n"
      "module m;\n"
      "  other inst();\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ProgramExclusion, AnInstanceOfTheProgramItselfIsReported) {
  EXPECT_TRUE(
      ReportedAlone("program p;\n"
                    "  p inst();\n"
                    "endprogram\n",
                    kInst, 2));
}

TEST(NestedProgramEnd,
     DISABLED_AModuleEndingBeforeTheNestedEndprogramIsReported) {
  auto r = Parse(
      "module m;\n"
      "  program p;\n"
      "    initial begin end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "endprogram", 4, "24.3"));
}

TEST(NestedProgramEnd, ANestedEndprogramBeforeEndmoduleIsAccepted) {
  auto r = Parse(
      "module m;\n"
      "  program p;\n"
      "    initial begin end\n"
      "  endprogram\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(NestedProgramEnd,
     DISABLED_AnInterfaceEndingBeforeTheNestedEndprogramIsReported) {
  auto r = Parse(
      "interface bus;\n"
      "  program p;\n"
      "    initial begin end\n"
      "endinterface\n");
  EXPECT_TRUE(ReportedError(r.diags, "endprogram", 4, "24.3"));
}

TEST(NestedProgramEnd, ANestedEndprogramBeforeEndinterfaceIsAccepted) {
  auto r = Parse(
      "interface bus;\n"
      "  program p;\n"
      "    initial begin end\n"
      "  endprogram\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ProgramTimeunitRepeat, AMatchingLaterTimeunitIsAccepted) {
  auto r = Parse(
      "program p;\n"
      "  timeunit 1ns;\n"
      "  int x;\n"
      "  timeunit 1ns;\n"
      "endprogram\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ProgramTimeunitRepeat, AMismatchedLaterTimeunitIsReported) {
  auto r = Parse(
      "program p;\n"
      "  timeunit 1ns;\n"
      "  int x;\n"
      "  timeunit 1ps;\n"
      "endprogram\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "timeunit does not match prior declaration", 4, "3.14.2.2"));
}

}  // namespace
