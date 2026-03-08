#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ParserA27, ElabTaskAutomaticLifetime) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  task automatic my_task(input int n);\n"
      "    #10;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elab13031, StaticTaskElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task static counter();\n"
      "    int cnt;\n"
      "    cnt = cnt + 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(Elab13031, StaticVarInAutoTaskElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task automatic work();\n"
      "    static int count = 0;\n"
      "    count = count + 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(Elab13031, AutoVarInStaticTaskElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task static work();\n"
      "    automatic int temp = 0;\n"
      "    temp = temp + 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}
