#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §13.3.2: Automatic task local variable in nonblocking assignment is an error.
TEST(Elab13032, AutoTaskLocalInNonblockingAssignError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task automatic t();\n"
      "    int x;\n"
      "    x <= 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §13.3.2: Module-level variable in nonblocking assignment inside auto task is ok.
TEST(Elab13032, AutoTaskModuleVarNonblockingOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  task automatic t();\n"
      "    x <= 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §13.3.2: Static task local variable in nonblocking assignment is ok.
TEST(Elab13032, StaticTaskLocalInNonblockingOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task static t();\n"
      "    int x;\n"
      "    x <= 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §13.3.2: Default task (static) local variable in nonblocking assignment is ok.
TEST(Elab13032, DefaultTaskLocalInNonblockingOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task t();\n"
      "    int x;\n"
      "    x <= 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §13.3.2: Automatic task arg in nonblocking assignment is an error.
TEST(Elab13032, AutoTaskArgInNonblockingAssignError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task automatic t(output int y);\n"
      "    y <= 5;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §13.3.2: Automatic task — blocking assignment to local is ok.
TEST(Elab13032, AutoTaskLocalBlockingAssignOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task automatic t();\n"
      "    int x;\n"
      "    x = 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
