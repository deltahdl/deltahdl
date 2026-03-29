#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §8.28(a): Structs are strictly static — usable immediately without new.
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

// §8.28(a): Class declaration does not create the object — handle is null.
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

// §8.28(a): After new, the class object exists and is no longer null.
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

// §8.28(b): Handles provide pointer-like semantics — two handles to the
// same object see each other's mutations.
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

// §8.28(a,b): Struct assignment copies value — modifying the copy does not
// affect the original, unlike class handle assignment.
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

}  // namespace
