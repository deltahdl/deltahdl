#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ClassesAndStructures, StructMemberAccessWithoutNew) {
  EXPECT_EQ(RunAndGet(
      "module t;\n"
      "  typedef struct { int x; int y; } point_t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    point_t p;\n"
      "    p.x = 10;\n"
      "    p.y = 20;\n"
      "    result = p.x + p.y;\n"
      "  end\n"
      "endmodule\n", "result"), 30u);
}

TEST(ClassesAndStructures, ClassHandleNullBeforeNew) {
  EXPECT_EQ(RunAndGet(
      "class C;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C obj;\n"
      "    result = (obj == null);\n"
      "  end\n"
      "endmodule\n", "result"), 1u);
}

TEST(ClassesAndStructures, ClassHandleNonNullAfterNew) {
  EXPECT_EQ(RunAndGet(
      "class C;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C obj;\n"
      "    obj = new;\n"
      "    result = (obj != null);\n"
      "  end\n"
      "endmodule\n", "result"), 1u);
}

TEST(ClassesAndStructures, TwoHandlesSameObjectShareState) {
  EXPECT_EQ(RunAndGet(
      "class C;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C a, b;\n"
      "    a = new;\n"
      "    a.x = 5;\n"
      "    b = a;\n"
      "    b.x = 99;\n"
      "    result = a.x;\n"
      "  end\n"
      "endmodule\n", "result"), 99u);
}

TEST(ClassesAndStructures, StructAssignmentCopiesValue) {
  EXPECT_EQ(RunAndGet(
      "module t;\n"
      "  typedef struct { int x; } wrap_t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    wrap_t a, b;\n"
      "    a.x = 5;\n"
      "    b = a;\n"
      "    b.x = 99;\n"
      "    result = a.x;\n"
      "  end\n"
      "endmodule\n", "result"), 5u);
}

}
