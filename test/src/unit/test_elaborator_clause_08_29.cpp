#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ClassTypeElaboration, DynamicAllocationOk) {
  EXPECT_TRUE(
      ElabOk("class MyClass;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ClassTypeElaboration, MultipleClassTypesOk) {
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

TEST(ClassTypeElaboration, NullAssignmentOk) {
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
