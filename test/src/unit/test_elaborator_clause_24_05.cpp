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

}  // namespace
