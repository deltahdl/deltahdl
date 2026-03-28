
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ClassOverviewElaboration, ClassWithPropertiesAndMethodsElaborates) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  function int get_x();\n"
             "    get_x = x;\n"
             "  endfunction\n"
             "  task set_x(int val);\n"
             "    x = val;\n"
             "  endtask\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "  initial c = new;\n"
             "endmodule\n"));
}

TEST(ClassOverviewElaboration, ObjectDeclaredAsInputArgument) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  function void accept(input C other);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    automatic C a, b;\n"
             "    a = new;\n"
             "    b = new;\n"
             "    a.accept(b);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassOverviewElaboration, ObjectDeclaredAsOutputArgument) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  task make_copy(output C result);\n"
             "    result = new;\n"
             "  endtask\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    automatic C a, b;\n"
             "    a = new;\n"
             "    a.make_copy(b);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassOverviewElaboration, ObjectDeclaredAsInoutArgument) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  task swap(inout C other);\n"
             "  endtask\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    automatic C a, b;\n"
             "    a = new;\n"
             "    b = new;\n"
             "    a.swap(b);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassOverviewElaboration, ObjectDeclaredAsRefArgument) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  function void update(ref C other);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    automatic C a, b;\n"
             "    a = new;\n"
             "    b = new;\n"
             "    a.update(b);\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
