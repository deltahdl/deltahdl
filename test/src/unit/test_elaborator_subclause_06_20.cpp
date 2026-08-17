#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §6.20: "Constants are named data objects that never change. SystemVerilog
// provides three elaboration-time constants: parameter, localparam, and
// specparam." A procedural assignment that writes one breaks that sentence, and
// the sentence says nothing about the shape of the write or about where the
// statement making it stands. The cases in the numbered files beside this one
// cover the constants themselves; these cover the writes, one per shape the
// report used to be absent from.
//
// Every case here uses a parameter unless it says otherwise, because
// Elaborator::const_names_ takes the three kinds together and the report is the
// same for all three.

TEST(ConstAssignElaboration, ABitSelectWriteToAParameterIsReported) {
  // §11.5.1's bit-select selects one bit of a named object and stores into that
  // object, so the object written is the parameter and not the bit. This is the
  // shape with no lvalue validator behind it: the checks in
  // src/elaborator/elaborator_validate_operations_arrays.cpp judge whether a
  // select is well formed and never whether its target may be written.
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter logic [7:0] P = 8'hFF;\n"
      "  initial P[3] = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            3, "6.20"));
}

TEST(ConstAssignElaboration, APartSelectWriteToAParameterIsReported) {
  // The same shape with a range rather than a single index. It is a case of its
  // own because a repair that unwrapped one particular select form would reach
  // one and not the other.
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter logic [7:0] P = 8'hFF;\n"
      "  initial P[7:4] = 4'd0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            3, "6.20"));
}

TEST(ConstAssignElaboration, AConcatenationWriteToAParameterIsReported) {
  // §11.4.12 makes a concatenation a legal left-hand side, and each operand of
  // one is written. The parameter is the second operand, so a walk that asked
  // only about the first would pass this source.
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  integer i;\n"
      "  initial {i, P} = 8'd0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

TEST(ConstAssignElaboration, AWriteToAParameterFromATaskBodyIsReported) {
  // §9.2 counts a task a structured procedure. Its statements are not under
  // ModuleItem::body, so no unwrapping of the left-hand side reaches this
  // source: the body has to be walked for the write to be seen at all.
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  task t;\n"
      "    P = 7;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

TEST(ConstAssignElaboration, AWriteToAParameterFromAFunctionBodyIsReported) {
  // The same for a function, which ModuleItemKind gives a kind of its own, so a
  // repair naming the task kind alone would miss it.
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  function int fn;\n"
      "    P = 7;\n"
      "    return P;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

TEST(ConstAssignElaboration, AWriteToAParameterInsideForkIsReported) {
  // §9.3.2's fork-join keeps its statements in a member of its own, which the
  // walk did not visit.
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  initial fork\n"
      "    P = 1;\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

TEST(ConstAssignElaboration, AWriteToAParameterInAForInitializerIsReported) {
  // §12.7.1's for loop holds its initialization statements apart from its body,
  // and a write there is a write.
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  integer i;\n"
      "  initial for (P = 0; i < 2; i = i + 1) begin end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

TEST(ConstAssignElaboration, AWriteToAParameterInAForStepIsReported) {
  // The step assignments are a third member again, so this is a case of its own
  // rather than the initializer case restated.
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  integer i;\n"
      "  initial for (i = 0; i < 2; P = P + 1) begin end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

TEST(ConstAssignElaboration, ABitSelectWriteToALocalparamIsReported) {
  // §6.20 names localparam beside parameter, so a repair that narrowed to the
  // parameter keyword would leave this source accepted.
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  localparam logic [7:0] L = 8'hFF;\n"
      "  initial L[0] = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'L'",
                            3, "6.20"));
}

TEST(ConstAssignElaboration, AnElementWriteToAStringParameterIsReported) {
  // §6.16's string is indexed like any other named object, so a write to one of
  // its bytes writes the parameter. The report has to be made here: at run time
  // a parameter is an ordinary variable, and the write reaches the string path
  // in src/simulator/statement_assign_core.cpp with nothing left to refuse it.
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter string S = \"abc\";\n"
      "  initial S[0] = \"X\";\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'S'",
                            3, "6.20"));
}

TEST(ConstAssignElaboration, AWriteToAVariableThroughABitSelectIsAccepted) {
  // The other side of the first case: the same shape over a name that is not a
  // constant is a write the standard allows, so widening the check must not
  // have made every select of a name a report.
  EXPECT_TRUE(
      ElabOk("module top;\n"
             "  logic [7:0] v;\n"
             "  initial v[3] = 1'b0;\n"
             "endmodule\n"));
}

}  // namespace
