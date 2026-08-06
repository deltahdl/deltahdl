#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(DisableStatementElaboration, DisableNamedBlockElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a;\n"
      "  initial begin : blk\n"
      "    a = 1;\n"
      "    disable blk;\n"
      "    a = 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DisableStatementElaboration, DisableTaskElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task my_task;\n"
      "    #10;\n"
      "  endtask\n"
      "  initial begin\n"
      "    disable my_task;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DisableStatementElaboration, DisableFromOtherProcessElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, x;\n"
      "  initial begin : outer\n"
      "    forever @(posedge clk) x = x + 1;\n"
      "  end\n"
      "  initial begin\n"
      "    #100;\n"
      "    disable outer;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules[0]->processes.size(), 2u);
}

TEST(DisableStatementElaboration, DisableFunctionRejectsWithError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int my_func(input int x);\n"
      "    return x;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    disable my_func;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(DisableStatementElaboration, DisableNamedBlockInFunctionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int f(input int x);\n"
      "    begin : blk\n"
      "      if (x == 0) disable blk;\n"
      "    end\n"
      "    return x;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DisableStatementElaboration, DisableOuterBlockFromNestedBlockElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a;\n"
      "  initial begin : outer\n"
      "    begin : inner\n"
      "      a = 1;\n"
      "      disable outer;\n"
      "    end\n"
      "    a = 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DisableStatementElaboration, DisableAutoTaskElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task automatic my_task;\n"
      "    #10;\n"
      "  endtask\n"
      "  initial begin\n"
      "    disable my_task;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DisableStatementElaboration, DisableOuterBlockFromInsideFunctionAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a;\n"
      "  function int f(input int x);\n"
      "    disable outer_blk;\n"
      "    return x;\n"
      "  endfunction\n"
      "  initial begin : outer_blk\n"
      "    int r;\n"
      "    r = f(1);\n"
      "    a = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DisableStatementElaboration, DisableOuterTaskFromInsideFunctionAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int f(input int x);\n"
      "    disable t;\n"
      "    return x;\n"
      "  endfunction\n"
      "  task t;\n"
      "    int r;\n"
      "    r = f(1);\n"
      "  endtask\n"
      "  initial t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
