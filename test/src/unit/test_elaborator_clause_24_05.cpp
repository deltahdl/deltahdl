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

// §24.5 says "program subroutines" -- the illegal-from-design rule covers
// functions as well as tasks. A design module calling a program function in an
// expression position must also be rejected.
TEST(ProgramSubroutineCall, ModuleCallingProgramFunctionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int x;\n"
      "  program p;\n"
      "    function int pfunc; return 7; endfunction\n"
      "  endprogram\n"
      "  initial x = p.pfunc();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

// §24.5: the illegal-call rule reaches a program function invoked from a
// continuous assignment in a design module. This travels a distinct elaborator
// code path from the procedural-body cases above (the continuous-assign walker
// rather than the statement walker), so it needs its own coverage.
TEST(ProgramSubroutineCall, ModuleContAssignCallingProgramFunctionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [7:0] w;\n"
      "  program p;\n"
      "    function logic [7:0] pfunc; return 8'd3; endfunction\n"
      "  endprogram\n"
      "  assign w = p.pfunc();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
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

// §24.5: a program may also call a subroutine declared in a design module. The
// illegal-call check keys off the caller's scope, so it must stay silent when a
// program invokes a task belonging to the enclosing design module.
TEST(ProgramSubroutineCall, ProgramCallingDesignModuleTaskElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int x;\n"
      "  task dtask(input int v); x = v; endtask\n"
      "  program p;\n"
      "    initial dtask(5);\n"
      "  endprogram\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
