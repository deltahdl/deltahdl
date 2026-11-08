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

TEST(ForceReleaseElaboration, VarLvalueForceReleaseElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial begin force x = 1; release x; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ForceReleaseElaboration, ForceNetElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  initial begin force w = 1'b1; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ForceReleaseElaboration, ForceConcatLhsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  initial begin force {a, b} = 2'b11; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ForceReleaseElaboration, ForceConstBitSelectNetElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire [7:0] bus;\n"
      "  initial begin force bus[3] = 1'b1; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ForceReleaseElaboration, ForceConstPartSelectNetElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire [7:0] bus;\n"
      "  initial begin force bus[7:4] = 4'hF; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ForceReleaseElaboration, ForceBitSelectVariableLhsIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  initial begin force data[3] = 1'b1; end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "bit-select or part-select of a variable is not a legal force LHS", 3,
      "10.6.2"));
}

TEST(ForceReleaseElaboration, ForcePartSelectVariableLhsIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  initial begin force data[3:0] = 4'hA; end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "bit-select or part-select of a variable is not a legal force LHS", 3,
      "10.6.2"));
}

TEST(ForceReleaseElaboration, ForceBitSelectUserNettypeNetIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  nettype logic [7:0] my_t;\n"
      "  my_t bus;\n"
      "  initial begin force bus[3] = 1'b1; end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "nettype is not a legal force LHS", 4, "10.6.2"));
}

TEST(ForceReleaseElaboration, ForcePartSelectUserNettypeNetIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  nettype logic [7:0] my_t;\n"
      "  my_t bus;\n"
      "  initial begin force bus[7:4] = 4'hF; end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "nettype is not a legal force LHS", 4, "10.6.2"));
}

TEST(ForceReleaseElaboration, ForceOnAMixedAssignmentVariableNamesItsOwnRule) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  assign x = 1'b0;\n"
      "  initial begin\n"
      "    x = 1'b1;\n"
      "    force x = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "force or release applied to variable 'x'", 6,
                            "10.6.2"));
}

TEST(ForceReleaseElaboration,
     ForceOnAVariableWithOnlyAContinuousAssignmentIsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  assign x = 1'b0;\n"
      "  initial force x = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ForceReleaseElaboration,
     ForceOnAVariableWithOnlyProceduralAssignmentsIsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial begin\n"
      "    x = 1'b0;\n"
      "    force x = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ForceReleaseElaboration, ForceConcatWithBitSelectVariableIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  wire w;\n"
      "  initial begin force {w, data[0]} = 2'b11; end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "bit-select or part-select of a variable is not a legal force LHS", 4,
      "10.6.2"));
}

TEST(ForceReleaseElaboration, ForceOfAnArrayElementIsNoBitSelect) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] out [0:3]; logic [7:0] b; int q[$]; int aa[string];\n"
      "  logic [7:0] sq [2][2]; struct { logic [7:0] f; } s;\n"
      "  initial begin\n"
      "    force {out[1], b} = 16'hABCD;\n"
      "    force q[0] = 9;\n"
      "    force aa[\"k\"] = 9;\n"
      "    force sq[1][0] = 8'h1;\n"
      "    force out[1][3] = 1'b1;\n"
      "    force s.f[0] = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line : {5u, 6u, 7u, 8u}) {
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "not a legal force LHS",
                               line, "10.6.2"));
  }
  for (uint32_t line : {9u, 10u}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "bit-select or part-select of a variable is not a legal force LHS",
        line, "10.6.2"));
  }
}

TEST(ForceReleaseElaboration, ForceOfAnUnpackedAggregateIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] out [0:3]; logic [7:0] sq [2][2];\n"
      "  typedef struct { int a; int b; } pair_t;\n"
      "  typedef union { int i; int j; } word_t;\n"
      "  pair_t s; pair_t ps [2]; word_t u, v;\n"
      "  initial begin\n"
      "    force out = '{8'h1, 8'h2, 8'h3, 8'h4};\n"
      "    force s = '{1, 2};\n"
      "    force out[1:2] = '{8'h1, 8'h2};\n"
      "    force sq[1] = '{8'h1, 8'h2};\n"
      "    force ps[0] = '{1, 2};\n"
      "    force u = v;\n"
      "    force s.a = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line : {7u, 8u, 9u, 10u, 11u, 12u}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "unpacked array, structure or union is not a legal force LHS", line,
        "10.6.2"));
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                               "bit-select or part-select", line, "10.6.2"));
  }
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "not a legal force LHS", 13,
                             "10.6.2"));
}

TEST(ForceReleaseElaboration, ForceParamBitSelectNetElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter P = 3;\n"
      "  wire [7:0] bus;\n"
      "  initial begin force bus[P] = 1'b1; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ForceReleaseElaboration, ForceLocalparamPartSelectNetElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam HI = 7;\n"
      "  localparam LO = 4;\n"
      "  wire [7:0] bus;\n"
      "  initial begin force bus[HI:LO] = 4'hF; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ForceReleaseElaboration, ForceConcatWithNetBitSelectElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  wire [7:0] bus;\n"
      "  initial begin force {w, bus[3]} = 2'b11; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ForceReleaseElaboration,
     ReleaseOnAMixedAssignmentVariableNamesItsOwnRule) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  assign x = 1'b0;\n"
      "  initial begin\n"
      "    x = 1'b1;\n"
      "    release x;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "force or release applied to variable 'x'", 6,
                            "10.6.2"));
}

TEST(ForceReleaseElaboration, ForceBitSelectVariableLhsInARandcaseArmIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  initial randcase\n"
      "    1 : force data[3] = 1'b1;\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "bit-select or part-select of a variable is not a legal force LHS", 4,
      "10.6.2"));
}

TEST(ForceReleaseElaboration, ForceOfAWholeVariableInARandcaseArmIsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  initial randcase\n"
      "    1 : force data = 8'hFF;\n"
      "  endcase\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ForceReleaseElaboration, ForceBitSelectVariableLhsInARandsequenceIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { force data[3] = 1'b1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "bit-select or part-select of a variable is not a legal force LHS", 5,
      "10.6.2"));
}

TEST(ForceReleaseElaboration,
     ForceInARandcaseArmOverAMixedlyAssignedVariableIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  assign x = 1'b0;\n"
      "  initial begin\n"
      "    x = 1'b1;\n"
      "    randcase\n"
      "      1 : force x = 1'b1;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "force or release applied to variable 'x'", 7,
                            "10.6.2"));
}

TEST(ForceReleaseElaboration, ForceOverAMemberQualifiedMixedTargetIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef struct packed { logic f; } s_t;\n"
      "  s_t v;\n"
      "  logic a, b;\n"
      "  assign v = a;\n"
      "  initial v.f = b;\n"
      "  initial force v.f = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "force or release applied to variable 'v', which "
                            "is assigned by a mixture of continuous and "
                            "procedural assignments",
                            7, "10.6.2"));
}

TEST(ForceReleaseElaboration, ForceNonConstantSelectOfNetIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  wire [7:0] bus;\n"
      "  int i;\n"
      "  initial force bus[i] = 1'b1;\n"
      "  initial force {bus[i +: 2], bus[0]} = 3'b0;\n"
      "  initial force bus[3:0] = 4'h0;\n"
      "endmodule\n",
      f);
  for (uint32_t line : {4u, 5u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "bit-select or part-select of a net in a force "
                              "LHS must be constant",
                              line, "10.6.2"));
  }
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "bit-select or part-select of a net in a force "
                             "LHS must be constant",
                             6, "10.6.2"));
}

TEST(ForceReleaseElaboration, ForceTargetRulesReachSubroutineBodies) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  task tk; force data[3] = 1'b1; endtask\n"
      "  function void fn(); force data[2] = 1'b1; endfunction\n"
      "endmodule\n",
      f);
  for (uint32_t line : {3u, 4u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "bit-select or part-select of a variable is not "
                              "a legal force LHS",
                              line, "10.6.2"));
  }
}

TEST(ForceReleaseElaboration, ForceOfAConstantIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  parameter P = 1; localparam L = 2; specparam SP = 3;\n"
      "  typedef enum {A, B} e_t;\n"
      "  logic q; wire w;\n"
      "  initial begin\n"
      "    force P = 5;\n"
      "    force L = 5;\n"
      "    force SP = 5;\n"
      "    force A = 1;\n"
      "    force {w, L} = 2;\n"
      "    force q = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  const std::pair<const char*, uint32_t> kReports[] = {
      {"P", 6}, {"L", 7}, {"SP", 8}, {"A", 9}, {"L", 10}};
  for (const auto& [name, line] : kReports) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        std::format("force of constant '{}', which is not a variable or a net",
                    name),
        line, "10.6.2"));
  }
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), "force of constant", 11, "10.6.2"));
}

TEST(ForceReleaseElaboration, ForceLhsInsideGenerateBlocksIsChecked) {
  EXPECT_TRUE(RejectedInsideGenerateBlocks(
      {"", "logic [3:0] v;", "initial force v[0] = 1;"},
      "bit-select or part-select of a variable is not a legal force LHS",
      "10.6.2"));
  EXPECT_TRUE(AcceptedInsideGenerateBlocks(
      {"", "logic [3:0] v;", "initial force v = 1;"}));
}

TEST(ForceReleaseElaboration,
     ForceOverMixedAssignmentsInsideGenerateBlocksIsRejected) {
  {
    ElabFixture f;
    ElaborateSrc(
        "module m;\n"
        "  logic v;\n"
        "  assign v = 1;\n"
        "  if (1) begin : g\n"
        "    initial v = 0;\n"
        "    initial force v = 1;\n"
        "  end\n"
        "endmodule\n",
        f);
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "force or release applied to variable 'v', which is assigned by a "
        "mixture of continuous and procedural assignments",
        6, "10.6.2"));
  }
  {
    ElabFixture f;
    ElaborateSrc(
        "module m;\n"
        "  logic v;\n"
        "  assign v = 1;\n"
        "  if (1) begin : g\n"
        "    initial release v;\n"
        "    initial v = 0;\n"
        "  end\n"
        "endmodule\n",
        f);
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "force or release applied to variable 'v', which is assigned by a "
        "mixture of continuous and procedural assignments",
        5, "10.6.2"));
  }
  {
    ElabFixture f;
    ElaborateSrc(
        "module m;\n"
        "  logic v;\n"
        "  assign v = 1;\n"
        "  initial force v = 1;\n"
        "  if (1) begin : g\n"
        "    initial v = 0;\n"
        "  end\n"
        "endmodule\n",
        f);
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "force or release applied to variable 'v', which is assigned by a "
        "mixture of continuous and procedural assignments",
        4, "10.6.2"));
  }
  {
    ElabFixture f;
    ElaborateSrc(
        "module m;\n"
        "  if (1) begin : g\n"
        "    logic v;\n"
        "    initial force v = 1;\n"
        "    initial v = 0;\n"
        "    assign v = 1;\n"
        "  end\n"
        "endmodule\n",
        f);
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "force or release applied to variable 'v', which is assigned by a "
        "mixture of continuous and procedural assignments",
        4, "10.6.2"));
  }
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic v;\n"
             "  if (1) begin : g\n"
             "    initial v = 0;\n"
             "    initial force v = 1;\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
