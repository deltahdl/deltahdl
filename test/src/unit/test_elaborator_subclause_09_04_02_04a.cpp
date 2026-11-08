#include <gtest/gtest.h>

#include <initializer_list>

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

TEST(SequenceEventElaboration, AnArgumentIsJudgedByTheVariableItNames) {
  ElabFixture f;
  ElaborateSrc(
      "module m; logic clk, v0;\n"
      "  sequence s(x); @(posedge clk) x; endsequence\n"
      "  task automatic tk(input logic f);\n"
      "    static logic st;\n"
      "    @(s(1'b1)) ;\n"
      "    @(s(st)) ;\n"
      "    @(s(f)) ;\n"
      "  endtask\n"
      "  initial begin automatic logic v; @(s(v)); end\n"
      "  initial @(s(v0));\n"
      "endmodule\n",
      f);
  const char* const kMessage =
      "sequence event arguments shall not reference automatic variables";
  for (const int kLine : {7, 9}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, kLine, "9.4.2.4"))
        << kLine;
  }
  for (const int kLine : {5, 6, 10}) {
    EXPECT_FALSE(
        ReportedError(f.diag.Diagnostics(), kMessage, kLine, "9.4.2.4"))
        << kLine;
  }
}

}  // namespace
