#include <gtest/gtest.h>

#include <string>

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

TEST(PlaOutputTerms, ANetOutputInATaskIsRejected) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  logic [1:2] mem [1:1];\n"
      "  logic [1:2] in;\n"
      "  wire [1:1] w;\n"
      "  task t();\n"
      "    $async$and$array(mem, in, w);\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a PLA modeling system task writes its output "
                            "terms, so each must be a variable, not a net",
                            6, "20.16"));
}

TEST(PlaOutputTerms, AVariableOutputInATaskIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:2] mem [1:1];\n"
      "  logic [1:2] in;\n"
      "  logic [1:1] v;\n"
      "  task t();\n"
      "    $async$and$array(mem, in, v);\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PlaOutputTerms, ANetOutputInAFunctionIsRejected) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  logic [1:2] mem [1:1];\n"
      "  logic [1:2] in;\n"
      "  wire [1:1] w;\n"
      "  function void f();\n"
      "    $async$and$array(mem, in, w);\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a PLA modeling system task writes its output "
                            "terms, so each must be a variable, not a net",
                            6, "20.16"));
}

TEST(PlaOutputTerms, AVariableOutputInAFunctionIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:2] mem [1:1];\n"
      "  logic [1:2] in;\n"
      "  logic [1:1] v;\n"
      "  function void f();\n"
      "    $async$and$array(mem, in, v);\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PlaOutputTerms, ANetOutputInAProgramIsRejected) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "program p;\n"
      "  logic [1:2] mem [1:1];\n"
      "  logic [1:2] in;\n"
      "  wire [1:1] w;\n"
      "  initial $async$and$array(mem, in, w);\n"
      "endprogram\n"
      "module m;\n"
      "  p u();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a PLA modeling system task writes its output "
                            "terms, so each must be a variable, not a net",
                            5, "20.16"));
}

TEST(PlaOutputTerms, AVariableOutputInAProgramIsAccepted) {
  ElabFixture f;
  Elaborate(
      "program p;\n"
      "  logic [1:2] mem [1:1];\n"
      "  logic [1:2] in;\n"
      "  logic [1:1] v;\n"
      "  initial $async$and$array(mem, in, v);\n"
      "endprogram\n"
      "module m;\n"
      "  p u();\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PlaOutputTerms, ANetOutputInAnInterfaceIsRejected) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "interface i;\n"
      "  logic [1:2] mem [1:1];\n"
      "  logic [1:2] in;\n"
      "  wire [1:1] w;\n"
      "  initial $async$and$array(mem, in, w);\n"
      "endinterface\n"
      "module m;\n"
      "  i u();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a PLA modeling system task writes its output "
                            "terms, so each must be a variable, not a net",
                            5, "20.16"));
}

TEST(PlaOutputTerms, AVariableOutputInAnInterfaceIsAccepted) {
  ElabFixture f;
  Elaborate(
      "interface i;\n"
      "  logic [1:2] mem [1:1];\n"
      "  logic [1:2] in;\n"
      "  logic [1:1] v;\n"
      "  initial $async$and$array(mem, in, v);\n"
      "endinterface\n"
      "module m;\n"
      "  i u();\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PlaOutputTerms, ANetOutputInAnAlwaysBlockIsRejected) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  logic [1:2] mem [1:1];\n"
      "  logic [1:2] in;\n"
      "  wire [1:1] w;\n"
      "  always #1 $async$and$array(mem, in, w);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a PLA modeling system task writes its output "
                            "terms, so each must be a variable, not a net",
                            5, "20.16"));
}

TEST(PlaOutputTerms, AVariableOutputInAnAlwaysBlockIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:2] mem [1:1];\n"
      "  logic [1:2] in;\n"
      "  logic [1:1] v;\n"
      "  always #1 $async$and$array(mem, in, v);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PlaOutputTerms, DISABLED_ANetOutputInAClassMethodIsRejected) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  logic [1:2] mem [1:1];\n"
      "  logic [1:2] in;\n"
      "  wire [1:1] w;\n"
      "  class C;\n"
      "    task t();\n"
      "      $async$and$array(mem, in, w);\n"
      "    endtask\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a PLA modeling system task writes its output "
                            "terms, so each must be a variable, not a net",
                            7, "20.16"));
}

TEST(PlaOutputTerms, AVariableOutputInAClassMethodIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:2] mem [1:1];\n"
      "  logic [1:2] in;\n"
      "  logic [1:1] v;\n"
      "  class C;\n"
      "    task t();\n"
      "      $async$and$array(mem, in, v);\n"
      "    endtask\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PlaOutputTerms, DISABLED_ANetOutputInAGenerateBlockIsRejected) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  logic [1:2] mem [1:1];\n"
      "  logic [1:2] in;\n"
      "  wire [1:1] w;\n"
      "  if (1) begin : g\n"
      "    initial $async$and$array(mem, in, w);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a PLA modeling system task writes its output "
                            "terms, so each must be a variable, not a net",
                            6, "20.16"));
}

TEST(PlaOutputTerms, AVariableOutputInAGenerateBlockIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:2] mem [1:1];\n"
      "  logic [1:2] in;\n"
      "  logic [1:1] v;\n"
      "  if (1) begin : g\n"
      "    initial $async$and$array(mem, in, v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PlaOutputTerms, DISABLED_ANetOutputInAPackageTaskIsRejected) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "package pk;\n"
      "  logic [1:2] mem [1:1];\n"
      "  logic [1:2] in;\n"
      "  wire [1:1] w;\n"
      "  task t();\n"
      "    $async$and$array(mem, in, w);\n"
      "  endtask\n"
      "endpackage\n"
      "module m;\n"
      "  import pk::*;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a PLA modeling system task writes its output "
                            "terms, so each must be a variable, not a net",
                            6, "20.16"));
}

TEST(PlaOutputTerms, AVariableOutputInAPackageTaskIsAccepted) {
  ElabFixture f;
  Elaborate(
      "package pk;\n"
      "  logic [1:2] mem [1:1];\n"
      "  logic [1:2] in;\n"
      "  logic [1:1] v;\n"
      "  task t();\n"
      "    $async$and$array(mem, in, v);\n"
      "  endtask\n"
      "endpackage\n"
      "module m;\n"
      "  import pk::*;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PlaOutputTerms, DISABLED_ANetOutputInACompilationUnitTaskIsRejected) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "logic [1:2] mem [1:1];\n"
      "logic [1:2] in;\n"
      "wire [1:1] w;\n"
      "task t();\n"
      "  $async$and$array(mem, in, w);\n"
      "endtask\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a PLA modeling system task writes its output "
                            "terms, so each must be a variable, not a net",
                            5, "20.16"));
}

TEST(PlaOutputTerms, AVariableOutputInACompilationUnitTaskIsAccepted) {
  ElabFixture f;
  Elaborate(
      "logic [1:2] mem [1:1];\n"
      "logic [1:2] in;\n"
      "logic [1:1] v;\n"
      "task t();\n"
      "  $async$and$array(mem, in, v);\n"
      "endtask\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PlaOutputTerms, DISABLED_AHierarchicalNetOutputIsRejected) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module sub;\n"
      "  wire [1:1] w;\n"
      "endmodule\n"
      "module m;\n"
      "  logic [1:2] mem [1:1];\n"
      "  logic [1:2] in;\n"
      "  sub u();\n"
      "  initial $async$and$array(mem, in, u.w);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a PLA modeling system task writes its output "
                            "terms, so each must be a variable, not a net",
                            8, "20.16"));
}

TEST(PlaOutputTerms, AHierarchicalVariableOutputIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module sub;\n"
      "  logic [1:1] v;\n"
      "endmodule\n"
      "module m;\n"
      "  logic [1:2] mem [1:1];\n"
      "  logic [1:2] in;\n"
      "  sub u();\n"
      "  initial $async$and$array(mem, in, u.v);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

constexpr const char* kPlaTasks[] = {
    "$async$and$array", "$sync$and$array",   "$async$nand$array",
    "$sync$nand$array", "$async$or$array",   "$sync$or$array",
    "$async$nor$array", "$sync$nor$array",   "$async$and$plane",
    "$sync$and$plane",  "$async$nand$plane", "$sync$nand$plane",
    "$async$or$plane",  "$sync$or$plane",    "$async$nor$plane",
    "$sync$nor$plane"};

std::string PlaModule(const std::string& stmt) {
  return "module m;\n"
         "  logic [1:2] mem [1:1];\n"
         "  logic [1:2] in;\n"
         "  logic [1:1] v, c;\n"
         "  initial " +
         stmt +
         ";\n"
         "endmodule\n";
}

bool PlaReports(const std::string& stmt, const char* msg) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(PlaModule(stmt), f);
  return ReportedError(f.diag.Diagnostics(), msg, 5, "20.16");
}

TEST(PlaCallShape, EveryTaskWithItsThreeArgumentsIsAccepted) {
  for (const char* name : kPlaTasks) {
    ElabFixture f;
    Elaborate(PlaModule(std::string(name) + "(mem, in, v)"), f);
    EXPECT_FALSE(f.has_errors) << name;
  }
}

TEST(PlaCallShape, DISABLED_EveryTaskWithTwoArgumentsIsRejected) {
  for (const char* name : kPlaTasks) {
    EXPECT_TRUE(PlaReports(std::string(name) + "(mem, in)",
                           "a PLA modeling system task takes a memory, input "
                           "terms and output terms"))
        << name;
  }
}

TEST(PlaCallShape, DISABLED_EveryTaskWithFourArgumentsIsRejected) {
  for (const char* name : kPlaTasks) {
    EXPECT_TRUE(PlaReports(std::string(name) + "(mem, in, v, c)",
                           "a PLA modeling system task takes a memory, input "
                           "terms and output terms"))
        << name;
  }
}

TEST(PlaCallShape, DISABLED_EveryTaskWithAMemoryWordAsItsMemoryIsRejected) {
  for (const char* name : kPlaTasks) {
    EXPECT_TRUE(PlaReports(std::string(name) + "(mem[1], in, v)",
                           "the first argument of a PLA modeling system task "
                           "shall name its memory"))
        << name;
  }
}

TEST(PlaCallShape,
     DISABLED_EveryTaskWithAnExpressionAsItsOutputTermsIsRejected) {
  for (const char* name : kPlaTasks) {
    EXPECT_TRUE(PlaReports(std::string(name) + "(mem, in, v + 1)",
                           "the output terms of a PLA modeling system task "
                           "shall be a variable lvalue"))
        << name;
  }
}

TEST(PlaCallShape, DISABLED_EveryTaskUsedAsAValueIsRejected) {
  for (const char* name : kPlaTasks) {
    EXPECT_TRUE(PlaReports("c = " + std::string(name) + "(mem, in, v)",
                           "a PLA modeling system task cannot be used as an "
                           "expression"))
        << name;
  }
}

}  // namespace
