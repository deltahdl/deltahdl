#include <gtest/gtest.h>

#include <cstdint>
#include <format>
#include <initializer_list>
#include <utility>

#include "fixture_elaborator.h"
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
  // A concatenation LHS must be a concatenation *of variables*; a bit-select
  // element makes it a bit-select of a variable, which §10.6.1 forbids.
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
  // A concatenation of variables may itself contain a nested concatenation of
  // variables; with no bit/part-select anywhere in the tree the assign LHS is
  // still a concatenation of variables and elaborates cleanly.
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
  // The concatenation-of-variables rule reaches through nesting: a part-select
  // buried inside an inner concatenation still makes the LHS a part-select of a
  // variable and must be rejected.
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
  // §9.2.2.2 defines always_comb, and it does not change what a statement
  // inside it may contain. §10.6.1's rule against a bit-select or part-select
  // in a procedural assign LHS therefore reaches an assignment written in
  // always_comb exactly as it reaches the one AssignBitSelectLhsIsError writes
  // in initial. This case writes that same source with only the enclosing
  // procedure changed.
  //
  // It fails today because is_proc in
  // src/elaborator/elaborator_validate_matches.cpp names two of the six
  // procedural kinds ModuleItemKind declares, so
  // Elaborator::ValidateItemConstraints never calls CheckProceduralAssignLhs
  // on an always_comb body and no report is made at all. Nine calls sit behind
  // that one flag, so this case exists to pin the fix as a property of is_proc
  // rather than of any single check.
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

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so the fail arm of an immediate assertion is a statement
// position, and §10.6.1's rule reaches the procedural assign written there.
// This is the source AssignBitSelectLhsIsError writes in an initial block, with
// only the offending statement moved into that arm.
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

// The same §16.3 action-block arm holding an assign LHS §10.6.1 allows, which
// mirrors AssignSingularVariableLhs. It pins that reaching the arm reports on
// what the rule forbids rather than on every statement newly walked.
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

// §10.6.1 bounds an `assign` statement's target to a variable, and §6.20 and
// §6.19 make a parameter, a localparam, a specparam and a name an enumeration
// declares constants, none of them a variable. Each is reported, in a process
// and in a task alike, and an element of a concatenation is asked about as a
// target of its own; the variable `q` is not reported.
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

// §10.6.1 (printed page 257) bounds an `assign` statement's target to a
// variable or a concatenation of variables, and A.6.2 (printed page 1198)
// writes a `deassign`'s target as a variable_lvalue; only `force` and `release`
// (§10.6.2) take a net as well. A net named alone or within a concatenation is
// reported, in a process and in a task alike, while a block's own variable of
// the net's name is the block's and not the net.
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

}  // namespace
