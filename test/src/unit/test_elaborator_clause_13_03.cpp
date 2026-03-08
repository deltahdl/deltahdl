#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ParserA27, ElabTaskDeclInModule) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  task my_task(input int a);\n"
      "    $display(\"a=%0d\", a);\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elab1303, TaskWithOutputArgsElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  task compute(input int a, output int b);\n"
      "    b = a * 2;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(Elab1303, TaskWithInoutArgElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  task inc(inout int v);\n"
      "    v = v + 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(Elab1303, TaskEmptyBodyElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  task nop;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(Elab1303, TaskEnablesTaskElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  task inner;\n"
      "  endtask\n"
      "  task outer;\n"
      "    inner();\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}
