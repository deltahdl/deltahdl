#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(PlaAscendingOrder, AscendingMemoryAndTermsAreAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  wire [1:7] awire;\n"
      "  logic [1:3] breg;\n"
      "  initial $async$and$array(mem, awire, breg);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PlaAscendingOrder, DescendingMemoryWidthIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [7:1] mem [1:3];\n"
      "  wire [1:7] awire;\n"
      "  logic [1:3] breg;\n"
      "  initial $async$and$array(mem, awire, breg);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the memory of a PLA modeling system task has a "
                            "descending range; give it an ascending one",
                            5, "20.16.3"));
}

TEST(PlaAscendingOrder, DescendingMemoryDepthIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [3:1];\n"
      "  wire [1:7] awire;\n"
      "  logic [1:3] breg;\n"
      "  initial $async$and$array(mem, awire, breg);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the memory of a PLA modeling system task has a "
                            "descending range; give it an ascending one",
                            5, "20.16.3"));
}

TEST(PlaAscendingOrder, DescendingInputTermsAreRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  wire [7:1] awire;\n"
      "  logic [1:3] breg;\n"
      "  initial $async$and$array(mem, awire, breg);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "the input terms of a PLA modeling system task have a "
                    "descending range; give them an ascending one",
                    5, "20.16.3"));
}

TEST(PlaAscendingOrder, DescendingOutputTermsAreRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  wire [1:7] awire;\n"
      "  logic [3:1] breg;\n"
      "  initial $sync$or$plane(mem, awire, breg);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "the output terms of a PLA modeling system task have a "
                    "descending range; give them an ascending one",
                    5, "20.16.3"));
}

TEST(PlaAscendingOrder, EqualBoundRangeIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  wire [1:1] awire;\n"
      "  logic [1:3] breg;\n"
      "  initial $async$and$array(mem, awire, breg);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PlaAscendingOrder, ConcatenatedScalarTermsAreNotRangeChecked) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  wire a1, a2, a3, a4, a5, a6, a7;\n"
      "  logic b1, b2, b3;\n"
      "  initial $async$and$array(mem, {a1,a2,a3,a4,a5,a6,a7}, {b1,b2,b3});\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PlaAscendingOrder, DescendingMemoryWidthViaParameterIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  parameter P = 7;\n"
      "  logic [P:1] mem [1:3];\n"
      "  wire [1:7] awire;\n"
      "  logic [1:3] breg;\n"
      "  initial $async$and$array(mem, awire, breg);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the memory of a PLA modeling system task has a "
                            "descending range; give it an ascending one",
                            6, "20.16.3"));
}

TEST(PlaAscendingOrder, AscendingMemoryWidthViaParameterIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  parameter P = 7;\n"
      "  logic [1:P] mem [1:3];\n"
      "  wire [1:7] awire;\n"
      "  logic [1:3] breg;\n"
      "  initial $async$and$array(mem, awire, breg);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PlaAscendingOrder, DescendingMemoryDepthViaLocalparamIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  localparam Q = 3;\n"
      "  logic [1:7] mem [Q:1];\n"
      "  wire [1:7] awire;\n"
      "  logic [1:3] breg;\n"
      "  initial $async$and$array(mem, awire, breg);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the memory of a PLA modeling system task has a "
                            "descending range; give it an ascending one",
                            6, "20.16.3"));
}

TEST(PlaAscendingOrder, NonPlaTaskNameIsNotRangeChecked) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [7:1] mem [1:3];\n"
      "  wire [7:1] awire;\n"
      "  logic [3:1] breg;\n"
      "  initial $async$xor$array(mem, awire, breg);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PlaAscendingOrder, DescendingMemoryInAnAssertionPassStatementIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [7:1] amem [1:3];\n"
      "  wire [1:7] ain;\n"
      "  logic [1:3] aout;\n"
      "  logic ready;\n"
      "  initial assert (ready) $sync$nand$array(amem, ain, aout);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the memory of a PLA modeling system task has a "
                            "descending range; give it an ascending one",
                            6, "20.16.3"));
}

TEST(PlaAscendingOrder,
     DescendingInputTermsInAnAssertionFailStatementIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] bmem [1:3];\n"
      "  wire [7:1] bterm;\n"
      "  logic [1:3] bout;\n"
      "  logic done;\n"
      "  initial assert (done) else $async$nor$plane(bmem, bterm, bout);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "the input terms of a PLA modeling system task have a "
                    "descending range; give them an ascending one",
                    6, "20.16.3"));
}

TEST(PlaAscendingOrder, DescendingOutputTermsInARandcaseItemIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] cmem [1:3];\n"
      "  wire [1:7] cterm;\n"
      "  logic [3:1] cout;\n"
      "  initial randcase 1: $sync$and$plane(cmem, cterm, cout); endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "the output terms of a PLA modeling system task have a "
                    "descending range; give them an ascending one",
                    5, "20.16.3"));
}

TEST(PlaAscendingOrder,
     DescendingMemoryDepthInARandsequenceCodeBlockIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] dmem [3:1];\n"
      "  wire [1:7] dterm;\n"
      "  logic [1:3] dout;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { $async$or$array(dmem, dterm, dout); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the memory of a PLA modeling system task has a "
                            "descending range; give it an ascending one",
                            7, "20.16.3"));
}

TEST(PlaAscendingPlacement, DescendingInputsInATaskAreRejected) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  logic [1:2] mem [1:1];\n"
      "  logic [2:1] in;\n"
      "  logic [1:1] v;\n"
      "  task t();\n"
      "    $async$and$array(mem, in, v);\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "the input terms of a PLA modeling system task have a "
                    "descending range; give them an ascending one",
                    6, "20.16.3"));
}

TEST(PlaAscendingPlacement, DescendingInputsInAFunctionAreRejected) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  logic [1:2] mem [1:1];\n"
      "  logic [2:1] in;\n"
      "  logic [1:1] v;\n"
      "  function void f();\n"
      "    $async$and$array(mem, in, v);\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "the input terms of a PLA modeling system task have a "
                    "descending range; give them an ascending one",
                    6, "20.16.3"));
}

TEST(PlaAscendingPlacement, DescendingInputsInAProgramAreRejected) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "program p;\n"
      "  logic [1:2] mem [1:1];\n"
      "  logic [2:1] in;\n"
      "  logic [1:1] v;\n"
      "  initial $async$and$array(mem, in, v);\n"
      "endprogram\n"
      "module m;\n"
      "  p u();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "the input terms of a PLA modeling system task have a "
                    "descending range; give them an ascending one",
                    5, "20.16.3"));
}

TEST(PlaAscendingPlacement, DescendingInputsInAnInterfaceAreRejected) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "interface i;\n"
      "  logic [1:2] mem [1:1];\n"
      "  logic [2:1] in;\n"
      "  logic [1:1] v;\n"
      "  initial $async$and$array(mem, in, v);\n"
      "endinterface\n"
      "module m;\n"
      "  i u();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "the input terms of a PLA modeling system task have a "
                    "descending range; give them an ascending one",
                    5, "20.16.3"));
}

TEST(PlaAscendingPlacement, DescendingInputsInAnAlwaysBlockAreRejected) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  logic [1:2] mem [1:1];\n"
      "  logic [2:1] in;\n"
      "  logic [1:1] v;\n"
      "  always #1 $async$and$array(mem, in, v);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "the input terms of a PLA modeling system task have a "
                    "descending range; give them an ascending one",
                    5, "20.16.3"));
}

TEST(PlaAscendingPlacement,
     DISABLED_DescendingInputsInAClassMethodAreRejected) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  logic [1:2] mem [1:1];\n"
      "  logic [2:1] in;\n"
      "  logic [1:1] v;\n"
      "  class C;\n"
      "    task t();\n"
      "      $async$and$array(mem, in, v);\n"
      "    endtask\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "the input terms of a PLA modeling system task have a "
                    "descending range; give them an ascending one",
                    7, "20.16.3"));
}

TEST(PlaAscendingPlacement,
     DISABLED_DescendingInputsInAGenerateBlockAreRejected) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  logic [1:2] mem [1:1];\n"
      "  logic [2:1] in;\n"
      "  logic [1:1] v;\n"
      "  if (1) begin : g\n"
      "    initial $async$and$array(mem, in, v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "the input terms of a PLA modeling system task have a "
                    "descending range; give them an ascending one",
                    6, "20.16.3"));
}

TEST(PlaAscendingPlacement,
     DISABLED_DescendingInputsInAPackageTaskAreRejected) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "package pk;\n"
      "  logic [1:2] mem [1:1];\n"
      "  logic [2:1] in;\n"
      "  logic [1:1] v;\n"
      "  task t();\n"
      "    $async$and$array(mem, in, v);\n"
      "  endtask\n"
      "endpackage\n"
      "module m;\n"
      "  import pk::*;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "the input terms of a PLA modeling system task have a "
                    "descending range; give them an ascending one",
                    6, "20.16.3"));
}

TEST(PlaAscendingPlacement,
     DISABLED_DescendingInputsInACompilationUnitTaskAreRejected) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "logic [1:2] mem [1:1];\n"
      "logic [2:1] in;\n"
      "logic [1:1] v;\n"
      "task t();\n"
      "  $async$and$array(mem, in, v);\n"
      "endtask\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "the input terms of a PLA modeling system task have a "
                    "descending range; give them an ascending one",
                    5, "20.16.3"));
}

TEST(PlaAscendingPlacement, ADescendingPartSelectInputIsRejected) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  logic [1:2] mem [1:1];\n"
      "  logic [7:1] a;\n"
      "  logic [1:1] v;\n"
      "  initial $async$and$array(mem, a[2:1], v);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "the input terms of a PLA modeling system task have a "
                    "descending range; give them an ascending one",
                    5, "20.16.3"));
}

TEST(PlaAscendingPlacement, AnAscendingPartSelectInputIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:3] mem [1:1];\n"
      "  logic [1:7] a;\n"
      "  logic [1:1] v;\n"
      "  initial $async$and$array(mem, a[1:3], v);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PlaAscendingPlacement,
     DISABLED_AConcatenationHoldingADescendingVectorIsRejected) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  logic [1:4] mem [1:1];\n"
      "  logic [3:1] x;\n"
      "  logic y;\n"
      "  logic [1:1] v;\n"
      "  initial $async$and$array(mem, {x, y}, v);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "the input terms of a PLA modeling system task have a "
                    "descending range; give them an ascending one",
                    6, "20.16.3"));
}

TEST(PlaAscendingPlacement, AConcatenationHoldingAnAscendingVectorIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:4] mem [1:1];\n"
      "  logic [1:3] x;\n"
      "  logic y;\n"
      "  logic [1:1] v;\n"
      "  initial $async$and$array(mem, {x, y}, v);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PlaMemoryShape, DISABLED_ANetMemoryIsRejected) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  wire [1:2] mem [1:1];\n"
      "  logic [1:2] in;\n"
      "  logic [1:1] v;\n"
      "  initial $async$and$array(mem, in, v);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "the memory of a PLA modeling system task shall be an array of variables",
      5, "20.16.3"));
}

TEST(PlaMemoryShape, DISABLED_AMemoryWiderThanTheInputsIsRejected) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  logic [1:3] mem [1:2];\n"
      "  logic [1:2] in;\n"
      "  logic [1:2] v;\n"
      "  initial $async$and$array(mem, in, v);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "the memory of a PLA modeling system task shall be as wide "
                    "as the input terms and as deep as the output terms",
                    5, "20.16.3"));
}

TEST(PlaMemoryShape, DISABLED_AMemoryDeeperThanTheOutputsIsRejected) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  logic [1:2] mem [1:3];\n"
      "  logic [1:2] in;\n"
      "  logic [1:2] v;\n"
      "  initial $async$and$array(mem, in, v);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "the memory of a PLA modeling system task shall be as wide "
                    "as the input terms and as deep as the output terms",
                    5, "20.16.3"));
}

TEST(PlaMemoryShape, AMemoryMatchingTheTermsIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:2] mem [1:3];\n"
      "  logic [1:2] in;\n"
      "  logic [1:3] v;\n"
      "  initial $async$and$array(mem, in, v);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
