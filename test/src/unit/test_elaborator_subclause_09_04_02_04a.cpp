// §9.4.2.4 "Sequence events": a sequence instance used as an event control,
// written where such a control is normally written -- at the top of a task
// body.
//
// The cases writing it in one of the statement links
// Elaborator::WalkStmtsForSequenceEvents reaches only since it took its list
// from ForEachChildStmt are in test_elaborator_subclause_09_04_02_04b.cpp,
// which the 1000-line cap in .github/workflows/deltahdl.yml separated this
// file from.

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(SequenceEventElaboration, SequenceEventElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b, c;\n"
      "  sequence abc;\n"
      "    @(posedge clk) a ##1 b ##1 c;\n"
      "  endsequence\n"
      "  initial @(abc) $display(\"matched\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SequenceEventElaboration, SequenceEventArgumentResolvesToInstance) {
  // §9.4.2.4: the event_expression uses a sequence_instance whose argument is
  // a non-automatic signal from the enclosing scope.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, x, y;\n"
      "  sequence s(a, b);\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "  initial @(s(x, y)) $display(\"done\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SequenceEventElaboration, AutomaticVarAsSequenceArgErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  sequence s(logic x, logic y);\n"
      "    @(posedge clk) x ##1 y;\n"
      "  endsequence\n"
      "  task automatic t;\n"
      "    logic a, b;\n"
      "    @(s(a, b)) $display(\"matched\");\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "sequence event arguments shall not reference "
                            "automatic variables",
                            8, "9.4.2.4"));
}

}  // namespace
