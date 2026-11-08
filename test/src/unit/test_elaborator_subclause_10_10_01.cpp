#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string>
#include <utility>

#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

void RunAndExpectArray(
    SimFixture& f, RtlirDesign* design, const std::string& name,
    std::initializer_list<std::pair<int, uint64_t>> expected) {
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  for (const auto& [idx, val] : expected) {
    auto key = name + "[" + std::to_string(idx) + "]";
    auto* var = f.ctx.FindVariable(key);
    ASSERT_NE(var, nullptr) << key;
    EXPECT_EQ(var->value.ToUint64(), val) << key;
  }
}

TEST(UnpackedArrayConcatElaboration, ArrayItemInPositionalPatternError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef int AI3[1:3];\n"
      "  AI3 A3;\n"
      "  int A9[1:9];\n"
      "  initial A9 = '{A3, 4, 5, 6, 7, 8, 9};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array-typed identifier in assignment pattern "
                            "targeting unpacked array",
                            5, "10.9.1"));
}

TEST(UnpackedArrayConcatElaboration, ArrayItemInReplicatedPatternError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef int AI3[1:3];\n"
      "  AI3 A3;\n"
      "  int A9[1:9];\n"
      "  initial A9 = '{3{A3}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array-typed identifier in assignment pattern "
                            "targeting unpacked array",
                            5, "10.9.1"));
}

TEST(UnpackedArrayConcatElaboration, ReplicationTargetingUnpackedArrayError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A9[1:9];\n"
      "  initial A9 = {9{1}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication cannot target an unpacked array", 3,
                            "10.10.1"));
}

TEST(UnpackedArrayConcatElaboration, ArrayItemInDeclInitPatternError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef int AI3[1:3];\n"
      "  AI3 A3;\n"
      "  int A9[1:9] = '{A3, 4, 5, 6, 7, 8, 9};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array-typed identifier in assignment pattern "
                            "targeting unpacked array",
                            4, "10.9.1"));
}

TEST(UnpackedArrayConcatElaboration, ScalarItemsInDeclInitPatternOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A9[1:9] = '{1, 2, 3, 4, 5, 6, 7, 8, 9};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(UnpackedArrayConcatElaboration, ReplicationInDeclInitTargetingArrayError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A9[1:9] = {9{1}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication cannot target an unpacked array", 2,
                            "10.10.1"));
}

TEST(UnpackedArrayConcatElaboration, ReplicationInDeclInitPackedTargetOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [8:0] x = {9{1'b1}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(UnpackedArrayConcatElaboration,
     ArrayItemInReplicatedDeclInitPatternError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef int AI3[1:3];\n"
      "  AI3 A3;\n"
      "  int A9[1:9] = '{3{A3}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array-typed identifier in assignment pattern "
                            "targeting unpacked array",
                            4, "10.9.1"));
}

TEST(UnpackedArrayConcatElaboration, PositionalScalarPatternAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A9[1:9];\n"
      "  initial A9 = '{1, 2, 3, 4, 5, 6, 7, 8, 9};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(UnpackedArrayConcatElaboration, PatternReplicationIntoArrayAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A9[1:9];\n"
      "  initial A9 = '{9{1}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(UnpackedArrayConcatElaboration, ReplicationWithParameterCountRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int N = 9;\n"
      "  int A9[1:9];\n"
      "  initial A9 = {N{1}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication cannot target an unpacked array", 4,
                            "10.10.1"));
}

TEST(UnpackedArrayConcatSim, UnpackedArrayConcatScalarElements) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr [0:2];\n"
      "  initial begin\n"
      "    arr = {1, 2, 3};\n"
      "  end\n"
      "endmodule\n",
      f);
  RunAndExpectArray(f, design, "arr", {{0, 1}, {1, 2}, {2, 3}});
}

TEST(ArrayItemExpansionElaborates, ArrayItemExpansionElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A[2], B[2], C[4];\n"
      "  initial C = {A, B};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

TEST(UnpackedArrayConcatDescending, UnpackedArrayConcatDescending) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr [2:0];\n"
      "  initial begin\n"
      "    arr = {10, 20, 30};\n"
      "  end\n"
      "endmodule\n",
      f);
  RunAndExpectArray(f, design, "arr", {{2, 10}, {1, 20}, {0, 30}});
}

TEST(UnpackedArrayConcatElaboration,
     ReplicationTargetingArrayInAForkArmNames10_10_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int A2[1:2];\n"
      "  initial begin\n"
      "    fork\n"
      "      A2 = {2{1}};\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication cannot target an unpacked array", 5,
                            "10.10.1"));
}

TEST(UnpackedArrayConcatElaboration,
     ReplicationTargetingArrayInAnAssertionPassStatementNames10_10_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int A2[1:2];\n"
      "  logic ok;\n"
      "  initial assert (ok) A2 = {2{1}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication cannot target an unpacked array", 4,
                            "10.10.1"));
}

TEST(UnpackedArrayConcatElaboration,
     ReplicationTargetingArrayInAnAssertionFailStatementNames10_10_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int A2[1:2];\n"
      "  logic ok;\n"
      "  initial assert (ok) else A2 = {2{1}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication cannot target an unpacked array", 4,
                            "10.10.1"));
}

TEST(UnpackedArrayConcatElaboration,
     ReplicationTargetingArrayInARandcaseItemNames10_10_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int A2[1:2];\n"
      "  initial randcase 1: A2 = {2{1}}; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication cannot target an unpacked array", 3,
                            "10.10.1"));
}

TEST(UnpackedArrayConcatElaboration,
     ReplicationTargetingArrayInARandsequenceCodeBlockNames10_10_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int A2[1:2];\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { A2 = {2{1}}; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication cannot target an unpacked array", 5,
                            "10.10.1"));
}

TEST(UnpackedArrayConcatElaboration,
     ReplicationTargetingArrayInAForLoopInitializationNames10_10_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int A2[1:2];\n"
      "  int i;\n"
      "  initial for (A2 = {2{1}}; i < 1; i = i + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication cannot target an unpacked array", 4,
                            "10.10.1"));
}

TEST(UnpackedArrayConcatElaboration,
     ReplicationTargetingArrayInAForLoopStepNames10_10_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int A2[1:2];\n"
      "  int i;\n"
      "  initial for (i = 0; i < 1; A2 = {2{1}}) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication cannot target an unpacked array", 4,
                            "10.10.1"));
}

TEST(UnpackedArrayConcatElaboration, UntypedPatternItemIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int A3[1:3] = '{1, 2, 3}; int A9[1:9];\n"
      "  initial A9 = {A3, '{4, 5, 6, 7, 8, 9}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern without a type prefix outside "
                            "an assignment-like context",
                            3, "10.9"));
}

}  // namespace
