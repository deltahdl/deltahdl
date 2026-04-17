#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ProgramSubroutineCall, ModuleCallingProgramTaskIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  program p;\n"
      "    task ptask; endtask\n"
      "  endprogram\n"
      "  initial p.ptask();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

TEST(ProgramSubroutineCall, ModuleCallingProgramFunctionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int r;\n"
      "  program p;\n"
      "    function int pfunc(int x); return x + 1; endfunction\n"
      "  endprogram\n"
      "  initial r = p.pfunc(5);\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

TEST(ProgramSubroutineCall,
     ModuleAlwaysCallingProgramTaskIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic clk;\n"
      "  program p;\n"
      "    task ptask; endtask\n"
      "  endprogram\n"
      "  always @(posedge clk) p.ptask();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

TEST(ProgramSubroutineCall, ProgramCallingModuleTaskElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int x;\n"
      "  task mtask(input int v); x = v; endtask\n"
      "  program p;\n"
      "    initial mtask(7);\n"
      "  endprogram\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProgramSubroutineCall, ProgramCallingModuleFunctionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int r;\n"
      "  function int mfunc(int x); return x + 1; endfunction\n"
      "  program p;\n"
      "    initial r = mfunc(41);\n"
      "  endprogram\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProgramSubroutineCall, ProgramCallingOtherProgramTaskElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int x;\n"
      "  program p1;\n"
      "    task p1task(input int v); x = v; endtask\n"
      "  endprogram\n"
      "  program p2;\n"
      "    initial p1.p1task(9);\n"
      "  endprogram\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProgramSubroutineCall, ProgramCallingOtherProgramFunctionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int r;\n"
      "  program p1;\n"
      "    function int p1func(int x); return x + 1; endfunction\n"
      "  endprogram\n"
      "  program p2;\n"
      "    initial r = p1.p1func(41);\n"
      "  endprogram\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
