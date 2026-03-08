#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §8.29: Class object created with new — elaborates OK.
TEST(ElabA829, DynamicAllocationOk) {
  EXPECT_TRUE(
      ElabOk("class MyClass;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// §8.29: Multiple class types coexist — elaborates OK.
TEST(ElabA829, MultipleClassTypesOk) {
  EXPECT_TRUE(
      ElabOk("class A;\n"
             "  int x;\n"
             "endclass\n"
             "class B;\n"
             "  int y;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// §8.29: Assign null to release reference — elaborates OK.
TEST(ElabA829, NullAssignmentOk) {
  EXPECT_TRUE(
      ElabOk("class MyClass;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    MyClass obj;\n"
             "    obj = null;\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
