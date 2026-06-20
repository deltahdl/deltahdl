#include "fixture_elaborator.h"

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

TEST(SequenceEventElaboration, SequenceEventWithIffGuardElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b, c, en;\n"
      "  sequence abc;\n"
      "    @(posedge clk) a ##1 b ##1 c;\n"
      "  endsequence\n"
      "  initial @(abc iff en) $display(\"matched\");\n"
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
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
