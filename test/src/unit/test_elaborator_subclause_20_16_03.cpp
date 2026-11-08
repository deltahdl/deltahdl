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

}  // namespace
