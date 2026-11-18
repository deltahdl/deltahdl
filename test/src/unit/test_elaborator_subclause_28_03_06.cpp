#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(GateArrayConnection, MatchingWidthBroadcastElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, y;\n"
      "  and g[0:3](y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(GateArrayConnection, DistributeWidthElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire [3:0] y, a, b;\n"
      "  and g[0:3](y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(GateArrayConnection, MixedBroadcastAndDistributePerTerminalElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire [3:0] y;\n"
      "  wire a, b;\n"
      "  and g[0:3](y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(GateArrayConnection, ParameterizedArrayRangeDistributesAcrossInstances) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter N = 4;\n"
      "  wire [3:0] y, a, b;\n"
      "  and g[0:N-1](y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(GateArrayConnection, ParameterizedArrayRangeTooFewBitsIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  parameter N = 4;\n"
      "  wire [1:0] y;\n"
      "  wire a, b;\n"
      "  and g[0:N-1](y, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "gate or primitive array terminal width does not "
                            "match",
                            5, "28.3.6"));
}

TEST(GateArrayConnection, TooFewBitsOnArrayPortIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire [1:0] y;\n"
      "  wire a, b;\n"
      "  and g[0:3](y, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "gate or primitive array terminal width does not "
                            "match",
                            4, "28.3.6"));
}

TEST(GateArrayConnection, TooManyBitsOnArrayPortIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire [7:0] y;\n"
      "  wire a, b;\n"
      "  and g[0:3](y, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "gate or primitive array terminal width does not "
                            "match",
                            4, "28.3.6"));
}

TEST(GateArrayConnection, ScalarInterconnectCannotBroadcastAcrossArray) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  interconnect ic;\n"
      "  wire a, b;\n"
      "  and g[0:3](ic, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "interconnect terminal of a gate or primitive "
                            "instance array",
                            4, "28.3.6"));
}

TEST(GateArrayConnection, InterconnectWidthEqualToArrayLengthElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  interconnect [3:0] ic;\n"
      "  wire a, b;\n"
      "  and g[0:3](ic, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(GateArrayConnection, ASelectOrConcatenationOfTheWrongWidthIsReported) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire [7:0] y;\n"
      "  wire a, b, c, o;\n"
      "  and g[3:0] (y[2:0], a, b);\n"
      "  and h[3:0] (o, {a, b}, c);\n"
      "endmodule\n",
      f);
  for (int line : {4, 5}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "gate or primitive array terminal width does not "
                              "match",
                              line, "28.3.6"))
        << line;
  }
}

TEST(GateArrayConnection, AnOperatorExpressionOfTheWrongWidthIsReported) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire [2:0] s;\n"
      "  wire o;\n"
      "  and h[3:0] (o, ~s, 1'b1);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "gate or primitive array terminal width does not "
                            "match",
                            4, "28.3.6"));
}

TEST(GateArrayConnection, ALiteralOfTheWrongWidthIsReported) {
  for (const char* literal : {"2'b01", "1"}) {
    ElabFixture f;
    Elaborate(std::string("module m;\n"
                          "  wire [3:0] o;\n"
                          "  wire a;\n"
                          "  and g[3:0] (o, ") +
                  literal +
                  ", a);\n"
                  "endmodule\n",
              f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "gate or primitive array terminal width does not "
                              "match",
                              4, "28.3.6"))
        << literal;
  }
}

TEST(GateArrayConnection, ASubarrayOfTheWrongWidthIsReported) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire [1:0][1:0] p;\n"
      "  wire [3:0] o;\n"
      "  wire a;\n"
      "  and g[3:0] (o, p[1], a);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "gate or primitive array terminal width does not "
                            "match",
                            5, "28.3.6"));
}

constexpr const char* kInterconnectOnGateArray =
    "interconnect terminal of a gate or primitive instance array";
constexpr const char* kInterconnectOnModuleArray =
    "interconnect connected to a module instance array must have a "
    "bit-length equal to the instance-array length";

TEST(GateArrayConnection, AScalarInterconnectPortCannotBroadcastAcrossArray) {
  ElabFixture f;
  Elaborate(
      "module m(output interconnect ic);\n"
      "  wire a, b;\n"
      "  and g[0:3](ic, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kInterconnectOnGateArray, 3,
                            "28.3.6"));
}

TEST(GateArrayConnection, AnInterconnectPortAsWideAsTheArrayElaborates) {
  ElabFixture f;
  Elaborate(
      "module m(output interconnect [3:0] ic);\n"
      "  wire a, b;\n"
      "  and g[0:3](ic, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

std::string ModuleArrayOn(const std::string& header, const std::string& decl) {
  return "module c(input wire p);\nendmodule\n" + header + decl +
         "  c u[0:3] (.p(ic));\n"
         "endmodule\n";
}

TEST(ModuleArrayConnection, DISABLED_AnInterconnectOfAnotherWidthIsReported) {
  for (const std::string& decl :
       {"  interconnect ic;\n", "  interconnect [2:0] ic;\n"}) {
    ElabFixture f;
    Elaborate(ModuleArrayOn("module m;\n", decl), f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kInterconnectOnModuleArray,
                              5, "28.3.6"))
        << decl;
  }
  ElabFixture f;
  Elaborate(ModuleArrayOn("module m(input interconnect ic);\n", ""), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kInterconnectOnModuleArray, 4,
                            "28.3.6"));
}

TEST(ModuleArrayConnection, AnInterconnectAsWideAsTheArrayElaborates) {
  ElabFixture f;
  Elaborate(ModuleArrayOn("module m;\n", "  interconnect [3:0] ic;\n"), f);
  EXPECT_FALSE(f.has_errors);
  ElabFixture g;
  Elaborate(ModuleArrayOn("module m(input interconnect [3:0] ic);\n", ""), g);
  EXPECT_FALSE(g.has_errors);
}

constexpr const char* kTerminalWidth =
    "gate or primitive array terminal width does not match";

std::string InEachBlock(const std::string& block_open,
                        const std::string& block_close,
                        const std::string& module_decl, const std::string& prim,
                        int out_width) {
  return "primitive u(output y, input a);\n"
         "  table 0 : 0; 1 : 1; endtable\n"
         "endprimitive\n"
         "module m;\n" +
         module_decl + block_open + "    wire [" +
         std::to_string(out_width - 1) +
         ":0] out;\n"
         "    wire in;\n"
         "    " +
         prim + " b [3:0] (out, in);\n" + block_close + "endmodule\n";
}

struct BlockText {
  const char* open;
  const char* close;
};

constexpr BlockText kBlocks[] = {
    {"  if (1) begin\n", "  end\n"},
    {"  case (1) 1: begin\n", "  end endcase\n"},
    {"  for (genvar i = 0; i < 1; i++) begin\n", "  end\n"}};

TEST(GateArrayConnection, DISABLED_AGenerateBlocksNetIsMeasuredAsDeclared) {
  for (const auto& [open, close] : kBlocks) {
    for (const std::string& prim : {"buf", "u"}) {
      for (const std::string& module_decl : {"", "  wire [3:0] out;\n"}) {
        ElabFixture f;
        Elaborate(InEachBlock(open, close, module_decl, prim, 3), f);
        EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kTerminalWidth,
                                  module_decl.empty() ? 8 : 9, "28.3.6"))
            << open << prim << module_decl;
      }
      for (const std::string& module_decl : {"", "  wire out;\n"}) {
        ElabFixture f;
        Elaborate(InEachBlock(open, close, module_decl, prim, 4), f);
        EXPECT_FALSE(f.has_errors) << open << prim << module_decl;
      }
    }
  }
}

}  // namespace
