#include "fixture_elaborator.h"

namespace {

TEST(SystemNameElaboration, SystemTaskInInitialElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  initial $display(\"hello\");\n"
             "endmodule\n"));
}

TEST(SystemNameElaboration, SystemFunctionInAssignElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [31:0] w;\n"
             "  assign w = $clog2(16);\n"
             "endmodule\n"));
}

TEST(SystemNameElaboration, MultipleSystemTasksElaborate) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] x;\n"
             "  initial begin\n"
             "    x = 8'd1;\n"
             "    $display(\"x=%0d\", x);\n"
             "    $display(\"done\");\n"
             "  end\n"
             "endmodule\n"));
}

TEST(SystemNameElaboration, SystemFunctionInExpressionElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] result;\n"
             "  initial result = $clog2(32) + 8'd1;\n"
             "endmodule\n"));
}

TEST(SystemNameElaboration, SystemTaskWithNoArgsElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  initial $finish;\n"
             "endmodule\n"));
}

TEST(SystemNameElaboration, SystemTaskInFunctionBodyElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  function void f;\n"
             "    $display(\"in func\");\n"
             "  endfunction\n"
             "  initial f();\n"
             "endmodule\n"));
}

TEST(SystemNameElaboration, SystemFunctionWithDataTypeArgElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [31:0] w;\n"
             "  assign w = $bits(logic [7:0]);\n"
             "endmodule\n"));
}

TEST(SystemNameElaboration, EmbeddedDollarSystemCallElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  initial $test$plusargs(\"flag\");\n"
             "endmodule\n"));
}

}  // namespace
