#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(PlaOutputTerms, VariableOutputIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  logic a;\n"
      "  logic b;\n"
      "  initial $async$and$array(mem, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PlaOutputTerms, NetOutputIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  logic a;\n"
      "  wire b;\n"
      "  initial $async$and$array(mem, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a PLA modeling system task writes its output "
                            "terms, so each must be a variable, not a net",
                            5, "20.16"));
}

TEST(PlaOutputTerms, ConcatenatedVariableOutputIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  logic a1, a2;\n"
      "  logic b1, b2, b3;\n"
      "  initial $sync$or$plane(mem, {a1, a2}, {b1, b2, b3});\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PlaOutputTerms, ConcatenatedOutputWithNetIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  logic a;\n"
      "  logic b1;\n"
      "  wire b2;\n"
      "  initial $async$nor$array(mem, a, {b1, b2});\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a PLA modeling system task writes its output "
                            "terms, so each must be a variable, not a net",
                            6, "20.16"));
}

TEST(PlaOutputTerms, NetInputWithVariableOutputIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  wire a;\n"
      "  logic b;\n"
      "  initial $sync$nand$plane(mem, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PlaOutputTerms, NonTableNameIsNotSubjectToTheRule) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  logic a;\n"
      "  wire b;\n"
      "  initial $async$xor$array(mem, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PlaOutputTerms, NameWithExtraComponentIsNotSubjectToTheRule) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  logic a;\n"
      "  wire b;\n"
      "  initial $async$and$array$extra(mem, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PlaOutputTerms, BitSelectOfVariableOutputIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  logic a;\n"
      "  logic [3:0] b;\n"
      "  initial $sync$or$array(mem, a, b[0]);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PlaOutputTerms, BitSelectOfNetOutputIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  logic a;\n"
      "  wire [3:0] b;\n"
      "  initial $async$and$array(mem, a, b[0]);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a PLA modeling system task writes its output "
                            "terms, so each must be a variable, not a net",
                            5, "20.16"));
}

TEST(PlaOutputTerms, OrLogicTaskRecognizedSoNetOutputRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  logic a;\n"
      "  wire b;\n"
      "  initial $async$or$array(mem, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a PLA modeling system task writes its output "
                            "terms, so each must be a variable, not a net",
                            5, "20.16"));
}

TEST(PlaOutputTerms, SyncNandPlaneTaskRecognizedSoNetOutputRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  logic a;\n"
      "  wire b;\n"
      "  initial $sync$nand$plane(mem, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a PLA modeling system task writes its output "
                            "terms, so each must be a variable, not a net",
                            5, "20.16"));
}

TEST(PlaOutputTerms, NetOutputInAnAssertionPassStatementIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] amem [1:3];\n"
      "  logic ain;\n"
      "  wire aout;\n"
      "  logic ready;\n"
      "  initial assert (ready) $sync$and$array(amem, ain, aout);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a PLA modeling system task writes its output "
                            "terms, so each must be a variable, not a net",
                            6, "20.16"));
}

TEST(PlaOutputTerms, NetOutputInAnAssertionFailStatementIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] fmem [1:3];\n"
      "  logic fin;\n"
      "  wire fout;\n"
      "  logic done;\n"
      "  initial assert (done) else $async$nand$plane(fmem, fin, fout);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a PLA modeling system task writes its output "
                            "terms, so each must be a variable, not a net",
                            6, "20.16"));
}

TEST(PlaOutputTerms, NetOutputInARandcaseItemIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] nmem [1:3];\n"
      "  logic nin;\n"
      "  wire nout;\n"
      "  initial randcase 1: $sync$nor$array(nmem, nin, nout); endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a PLA modeling system task writes its output "
                            "terms, so each must be a variable, not a net",
                            5, "20.16"));
}

TEST(PlaOutputTerms, NetOutputInARandsequenceCodeBlockIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] rmem [1:3];\n"
      "  logic rin;\n"
      "  wire rout;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { $async$or$plane(rmem, rin, rout); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a PLA modeling system task writes its output "
                            "terms, so each must be a variable, not a net",
                            7, "20.16"));
}

}  // namespace
