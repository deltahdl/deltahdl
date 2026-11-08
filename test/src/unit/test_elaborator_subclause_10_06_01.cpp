#include <gtest/gtest.h>

#include <cstdint>
#include <format>
#include <initializer_list>
#include <utility>

#include "fixture_elaborator.h"
#include "helpers_generate_block_items.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ProceduralAssignDeassignElaboration, AssignSingularVariableLhs) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg q;\n"
      "  initial begin\n"
      "    assign q = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProceduralAssignDeassignElaboration, AssignConcatenationLhs) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    assign {a, b} = 2'b10;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProceduralAssignDeassignElaboration, AssignBitSelectLhsIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  reg [7:0] data;\n"
      "  initial begin\n"
      "    assign data[3] = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "bit-select or part-select in procedural assign LHS", 4, "10.6.1"));
}

TEST(ProceduralAssignDeassignElaboration, AssignPartSelectLhsIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  reg [7:0] data;\n"
      "  initial begin\n"
      "    assign data[3:0] = 4'hA;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "bit-select or part-select in procedural assign LHS", 4, "10.6.1"));
}

TEST(ProceduralAssignDeassignElaboration, DeassignSingularVariableLhs) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg q;\n"
      "  initial begin\n"
      "    assign q = 1;\n"
      "    deassign q;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProceduralAssignDeassignElaboration, DeassignConcatenationLhs) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    assign {a, b} = 2'b10;\n"
      "    deassign {a, b};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProceduralAssignDeassignElaboration, AssignVectorLhs) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg [15:0] vec;\n"
      "  initial begin\n"
      "    assign vec = 16'hDEAD;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProceduralAssignDeassignElaboration, AssignInAlwaysBlockElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg q;\n"
      "  reg clear, preset;\n"
      "  always @(clear or preset)\n"
      "    if (!clear)\n"
      "      assign q = 0;\n"
      "    else if (!preset)\n"
      "      assign q = 1;\n"
      "    else\n"
      "      deassign q;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProceduralAssignDeassignElaboration, AssignIndexedPartSelectLhsIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  reg [7:0] data;\n"
      "  initial begin\n"
      "    assign data[3+:4] = 4'hA;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "bit-select or part-select in procedural assign LHS", 4, "10.6.1"));
}

TEST(ProceduralAssignDeassignElaboration,
     AssignConcatWithBitSelectElemIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  reg [7:0] data;\n"
      "  reg b;\n"
      "  initial begin\n"
      "    assign {data[0], b} = 2'b10;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "bit-select or part-select in procedural assign LHS", 5, "10.6.1"));
}

TEST(ProceduralAssignDeassignElaboration,
     AssignConcatWithPartSelectElemIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  reg [7:0] data;\n"
      "  reg [3:0] b;\n"
      "  initial begin\n"
      "    assign {data[3:0], b} = 8'hAB;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "bit-select or part-select in procedural assign LHS", 5, "10.6.1"));
}

TEST(ProceduralAssignDeassignElaboration, AssignNestedConcatOfVariablesLhs) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a, b, c;\n"
      "  initial begin\n"
      "    assign {a, {b, c}} = 3'b101;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProceduralAssignDeassignElaboration, AssignNestedConcatWithSelectIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  reg [7:0] data;\n"
      "  reg a;\n"
      "  initial begin\n"
      "    assign {a, {data[3:0]}} = 5'b10101;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "bit-select or part-select in procedural assign LHS", 5, "10.6.1"));
}

TEST(ProceduralAssignDeassignElaboration, ReAssignSameVariableElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg q;\n"
      "  initial begin\n"
      "    assign q = 0;\n"
      "    assign q = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProceduralAssignDeassignElaboration,
     ProceduralContinuousAssignInAlwaysCombIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  reg [7:0] data;\n"
      "  always_comb begin\n"
      "    assign data[3] = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "bit-select or part-select in procedural assign LHS", 4, "10.6.1"));
}

TEST(ProceduralAssignDeassignElaboration,
     ProceduralAssignWithASelectLhsInAnAssertFailArmIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  reg [7:0] data;\n"
      "  initial assert (0) else\n"
      "    assign data[3] = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "bit-select or part-select in procedural assign LHS", 4, "10.6.1"));
}

TEST(ProceduralAssignDeassignElaboration,
     ProceduralAssignWithAWholeVariableLhsInAnAssertFailArmIsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg q;\n"
      "  initial assert (0) else\n"
      "    assign q = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProceduralAssignDeassignElaboration, AssignOfAConstantIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  parameter P = 1; localparam L = 2; specparam SP = 3;\n"
      "  typedef enum {A, B} e_t;\n"
      "  logic q;\n"
      "  initial begin\n"
      "    assign P = 5;\n"
      "    assign L = 5;\n"
      "    assign SP = 5;\n"
      "    assign A = 1;\n"
      "    assign {q, L} = 2;\n"
      "    assign q = 1;\n"
      "  end\n"
      "  task t; assign P = 6; endtask\n"
      "endmodule\n",
      f);
  const std::pair<const char*, uint32_t> kReports[] = {
      {"P", 6}, {"L", 7}, {"SP", 8}, {"A", 9}, {"L", 10}, {"P", 13}};
  for (const auto& [name, line] : kReports) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        std::format("procedural assign of constant '{}', which is not a "
                    "variable",
                    name),
        line, "10.6.1"));
  }
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "procedural assign of constant", 11, "10.6.1"));
}

TEST(ProceduralAssignDeassignElaboration, NetTargetOfAssignOrDeassignIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  logic v;\n"
      "  initial begin\n"
      "    assign w = 1'b0;\n"
      "    deassign w;\n"
      "    assign {v, w} = 2'b00;\n"
      "    force w = 1'b0;\n"
      "    release w;\n"
      "    assign v = 1'b0;\n"
      "  end\n"
      "  task t; assign w = 1'b1; endtask\n"
      "  initial begin : b\n"
      "    logic w;\n"
      "    assign w = 1'b0;\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line : {5u, 6u, 7u, 12u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "net 'w' cannot be the target of a procedural "
                              "assign or deassign",
                              line, "10.6.1"));
  }
  for (uint32_t line : {8u, 9u, 10u, 15u}) {
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                               "net 'w' cannot be the target of a procedural "
                               "assign or deassign",
                               line, "10.6.1"));
  }
}

TEST(ProceduralAssignDeassignElaboration, TargetInsideGenerateBlocksIsChecked) {
  EXPECT_TRUE(RejectedInsideGenerateBlocks(
      {"", "wire w;", "initial assign w = 1;"},
      "net 'w' cannot be the target of a procedural assign or deassign",
      "10.6.1"));
  EXPECT_TRUE(RejectedInsideGenerateBlocks(
      {"", "wire w;", "initial deassign w;"},
      "net 'w' cannot be the target of a procedural assign or deassign",
      "10.6.1"));
  EXPECT_TRUE(RejectedInsideGenerateBlocks(
      {"", "logic [3:0] v;", "initial assign v[0] = 1;"},
      "bit-select or part-select in procedural assign LHS", "10.6.1"));
  EXPECT_TRUE(AcceptedInsideGenerateBlocks(
      {"", "logic [3:0] v;", "initial assign v = 1;"}));
}

}  // namespace
