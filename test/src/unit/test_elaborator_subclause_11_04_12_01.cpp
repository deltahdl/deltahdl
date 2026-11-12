#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ReplicationElaboration, ReplicationInContAssign) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [1:0] x;\n"
      "  assign a = {4{x}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ReplicationElaboration, ReplicationInInitialBlock) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [1:0] x;\n"
      "  initial a = {4{x}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ReplicationElaboration, ConstantReplicationInParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter [31:0] P = {4{8'hFF}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ReplicationElaboration, ReplicationOnLhsOfBlockingAssign) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [1:0] a;\n"
      "  initial {4{a}} = 8'hFF;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an assignment target cannot contain a replication",
                            3, "11.4.12.1"));
}

TEST(ReplicationElaboration, ReplicationOnLhsOfNonblockingAssign) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [1:0] a;\n"
      "  initial {4{a}} <= 8'hFF;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an assignment target cannot contain a replication",
                            3, "11.4.12.1"));
}

TEST(ReplicationElaboration, ReplicationOnLhsOfContAssign) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [1:0] a;\n"
      "  assign {4{a}} = 8'hFF;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an assignment target cannot contain a replication",
                            3, "11.4.12.1"));
}

TEST(ReplicationElaboration, ReplicationInsideLhsConcat) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [1:0] a;\n"
      "  logic [3:0] b;\n"
      "  initial {b, {2{a}}} = 8'hFF;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an assignment target cannot contain a replication",
                            4, "11.4.12.1"));
}

TEST(ReplicationElaboration, ReplicationOnOutputPort) {
  ElabFixture f;
  ElaborateSrc(
      "module child(output [7:0] o);\n"
      "  assign o = 8'hAA;\n"
      "endmodule\n"
      "module m;\n"
      "  logic [1:0] a;\n"
      "  child u(.o({4{a}}));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication shall not appear in an output or "
                            "inout port connection",
                            6, "11.4.12.1"));
}

TEST(ReplicationElaboration, ReplicationOnInoutPort) {
  ElabFixture f;
  ElaborateSrc(
      "module child(inout [7:0] io);\n"
      "endmodule\n"
      "module m;\n"
      "  logic [1:0] a;\n"
      "  child u(.io({4{a}}));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication shall not appear in an output or "
                            "inout port connection",
                            5, "11.4.12.1"));
}

TEST(ReplicationElaboration, ReplicationOnInputPortOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input [7:0] i);\n"
      "endmodule\n"
      "module m;\n"
      "  logic [1:0] a;\n"
      "  child u(.i({4{a}}));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ReplicationElaboration, XMultiplierRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  initial a = {1'bx{1'b0}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication multiplier shall not contain x or z",
                            3, "11.4.12.1"));
}

TEST(ReplicationElaboration, ZMultiplierRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  initial a = {1'bz{1'b0}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication multiplier shall not contain x or z",
                            3, "11.4.12.1"));
}

TEST(ReplicationElaboration, ZeroReplicationStandaloneRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a;\n"
      "  logic [3:0] result;\n"
      "  initial result = {0{a}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a zero replication needs a positive-size operand "
                            "beside it in the same concatenation",
                            4, "11.4.12.1"));
}

TEST(ReplicationElaboration, ZeroReplicationInsideConcatOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a, b;\n"
      "  logic [3:0] result;\n"
      "  initial result = {a, {0{b}}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ReplicationElaboration, ZeroReplicationConcatAllZeroRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a, b;\n"
      "  logic [3:0] result;\n"
      "  initial result = {{0{a}}, {0{b}}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a zero replication needs a positive-size operand "
                            "beside it in the same concatenation",
                            4, "11.4.12.1"));
}

TEST(ReplicationElaboration, NegativeMultiplierRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  initial a = {-1{1'b0}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication multiplier shall not be negative", 3,
                            "11.4.12.1"));
}

TEST(ReplicationElaboration, ParameterZeroMultiplierStandaloneRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  parameter Z = 0;\n"
      "  logic [3:0] a;\n"
      "  logic [3:0] result;\n"
      "  initial result = {Z{a}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a zero replication needs a positive-size operand "
                            "beside it in the same concatenation",
                            5, "11.4.12.1"));
}

TEST(ReplicationElaboration, ParameterNegativeMultiplierRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  parameter Z = -1;\n"
      "  logic [7:0] a;\n"
      "  initial a = {Z{1'b0}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication multiplier shall not be negative", 4,
                            "11.4.12.1"));
}

TEST(ReplicationElaboration, ReplicationOnLvalueInAForkArmNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [1:0] a;\n"
      "  initial begin\n"
      "    fork\n"
      "      {4{a}} = 8'hFF;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an assignment target cannot contain a replication",
                            5, "11.4.12.1"));
}

TEST(ReplicationElaboration,
     ReplicationOnLvalueInAnAssertionPassStatementNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [1:0] a;\n"
      "  logic ok;\n"
      "  initial assert (ok) {4{a}} = 8'hFF;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an assignment target cannot contain a replication",
                            4, "11.4.12.1"));
}

TEST(ReplicationElaboration,
     ReplicationOnLvalueInAnAssertionFailStatementNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [1:0] a;\n"
      "  logic ok;\n"
      "  initial assert (ok) else {4{a}} = 8'hFF;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an assignment target cannot contain a replication",
                            4, "11.4.12.1"));
}

TEST(ReplicationElaboration, ReplicationOnLvalueInARandcaseItemNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [1:0] a;\n"
      "  initial randcase 1: {4{a}} = 8'hFF; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an assignment target cannot contain a replication",
                            3, "11.4.12.1"));
}

TEST(ReplicationElaboration,
     ReplicationOnLvalueInARandsequenceCodeBlockNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [1:0] a;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { {4{a}} = 8'hFF; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an assignment target cannot contain a replication",
                            5, "11.4.12.1"));
}

TEST(ReplicationElaboration,
     ReplicationOnLvalueInAForLoopInitializationNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [1:0] a;\n"
      "  int i;\n"
      "  initial for ({4{a}} = 8'hFF; i < 1; i = i + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an assignment target cannot contain a replication",
                            4, "11.4.12.1"));
}

TEST(ReplicationElaboration, ReplicationOnLvalueInAForLoopStepNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [1:0] a;\n"
      "  int i;\n"
      "  initial for (i = 0; i < 1; {4{a}} = 8'hFF) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an assignment target cannot contain a replication",
                            4, "11.4.12.1"));
}

TEST(ReplicationElaboration,
     ZeroReplicationStandaloneInAForkArmNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a;\n"
      "  logic [3:0] result;\n"
      "  initial begin\n"
      "    fork\n"
      "      result = {0{a}};\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a zero replication needs a positive-size operand "
                            "beside it in the same concatenation",
                            6, "11.4.12.1"));
}

TEST(ReplicationElaboration,
     ZeroReplicationStandaloneInAnAssertionPassStatementNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a;\n"
      "  logic [3:0] result;\n"
      "  logic ok;\n"
      "  initial assert (ok) result = {0{a}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a zero replication needs a positive-size operand "
                            "beside it in the same concatenation",
                            5, "11.4.12.1"));
}

TEST(ReplicationElaboration,
     ZeroReplicationStandaloneInAnAssertionFailStatementNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a;\n"
      "  logic [3:0] result;\n"
      "  logic ok;\n"
      "  initial assert (ok) else result = {0{a}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a zero replication needs a positive-size operand "
                            "beside it in the same concatenation",
                            5, "11.4.12.1"));
}

TEST(ReplicationElaboration,
     ZeroReplicationStandaloneInARandcaseItemNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a;\n"
      "  logic [3:0] result;\n"
      "  initial randcase 1: result = {0{a}}; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a zero replication needs a positive-size operand "
                            "beside it in the same concatenation",
                            4, "11.4.12.1"));
}

TEST(ReplicationElaboration,
     ZeroReplicationStandaloneInARandsequenceCodeBlockNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a;\n"
      "  logic [3:0] result;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { result = {0{a}}; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a zero replication needs a positive-size operand "
                            "beside it in the same concatenation",
                            6, "11.4.12.1"));
}

TEST(ReplicationElaboration,
     ZeroReplicationStandaloneInAForLoopInitializationNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a;\n"
      "  logic [3:0] result;\n"
      "  int i;\n"
      "  initial for (result = {0{a}}; i < 1; i = i + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a zero replication needs a positive-size operand "
                            "beside it in the same concatenation",
                            5, "11.4.12.1"));
}

TEST(ReplicationElaboration,
     ZeroReplicationStandaloneInAForLoopStepNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a;\n"
      "  logic [3:0] result;\n"
      "  int i;\n"
      "  initial for (i = 0; i < 1; result = {0{a}}) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a zero replication needs a positive-size operand "
                            "beside it in the same concatenation",
                            5, "11.4.12.1"));
}

TEST(ReplicationElaboration, XMultiplierInAForkArmNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = {1'bx{1'b0}};\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication multiplier shall not contain x or z",
                            5, "11.4.12.1"));
}

TEST(ReplicationElaboration,
     XMultiplierInAnAssertionPassStatementNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic ok;\n"
      "  initial assert (ok) a = {1'bx{1'b0}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication multiplier shall not contain x or z",
                            4, "11.4.12.1"));
}

TEST(ReplicationElaboration,
     XMultiplierInAnAssertionFailStatementNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic ok;\n"
      "  initial assert (ok) else a = {1'bx{1'b0}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication multiplier shall not contain x or z",
                            4, "11.4.12.1"));
}

TEST(ReplicationElaboration, XMultiplierInARandcaseItemNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  initial randcase 1: a = {1'bx{1'b0}}; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication multiplier shall not contain x or z",
                            3, "11.4.12.1"));
}

TEST(ReplicationElaboration,
     XMultiplierInARandsequenceCodeBlockNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { a = {1'bx{1'b0}}; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication multiplier shall not contain x or z",
                            5, "11.4.12.1"));
}

TEST(ReplicationElaboration,
     XMultiplierInAForLoopInitializationNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  int i;\n"
      "  initial for (a = {1'bx{1'b0}}; i < 1; i = i + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication multiplier shall not contain x or z",
                            4, "11.4.12.1"));
}

TEST(ReplicationElaboration, XMultiplierInAForLoopStepNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  int i;\n"
      "  initial for (i = 0; i < 1; a = {1'bx{1'b0}}) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication multiplier shall not contain x or z",
                            4, "11.4.12.1"));
}

TEST(ReplicationElaboration, ZeroReplicationInsideAReplicationBody) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic [7:0] y, z;\n"
      "  assign y = {2{{0{a}}, b}};\n"
      "  assign z = {2{{0{a}}}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a zero replication needs a positive-size operand "
                            "beside it in the same concatenation",
                            5, "11.4.12.1"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

TEST(ReplicationElaboration, NonConstantMultiplierOfNonStringReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int n = 2;\n"
      "  string s, r;\n"
      "  logic [7:0] y;\n"
      "  initial begin\n"
      "    y = {n{4'hA}};\n"
      "    r = {n{\"ab\"}};\n"
      "    r = {n{s}};\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication multiplier shall be a constant "
                            "expression",
                            6, "11.4.12.1"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

TEST(ReplicationElaboration, ReplicationAssignedWithinAnExpressionRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    ++{2{a}};\n"
      "    x = ({2{a}} = 8'h0);\n"
      "    {2{a}} += 8'h1;\n"
      "    x = {2{a}};\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line : {5u, 6u, 7u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "an assignment target cannot contain a "
                              "replication",
                              line, "11.4.12.1"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

TEST(
    ReplicationElaboration,
    AZeroReplicationAloneInANestedConcatenationOrASystemTaskArgumentIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  parameter P = 32;\n"
      "  wire [31:0] a, c;\n"
      "  assign c[31:0] = { {{32-P{1'b1}}}, a[P-1:0] };\n"
      "  initial\n"
      "    $displayb({32-P{1'b1}}, a[P-1:0]);\n"
      "endmodule\n",
      f);
  for (const int kLine : {4, 6}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "a zero replication needs a positive-size "
                              "operand beside it in the same concatenation",
                              kLine, "11.4.12.1"))
        << kLine;
  }
}

TEST(ReplicationElaboration,
     AZeroReplicationBesideAPositiveOperandIsAcceptedForEveryMultiplier) {
  for (const char* const kP : {"1", "16", "32"}) {
    ElabFixture f;
    ElaborateSrc(std::string("module m;\n"
                             "  parameter P = ") +
                     kP +
                     ";\n"
                     "  wire [31:0] a, b;\n"
                     "  assign b[31:0] = { {32-P{1'b1}}, a[P-1:0] };\n"
                     "endmodule\n",
                 f);
    EXPECT_FALSE(f.diag.HasErrors()) << kP;
  }
}

}  // namespace
