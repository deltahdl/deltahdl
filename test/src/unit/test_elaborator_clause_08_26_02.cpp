#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §8.26.2: Interface class extends another interface class — OK.
TEST(ElabA8262, InterfaceExtendsInterfaceOk) {
  EXPECT_TRUE(ElabOk(
      "interface class A;\n"
      "  pure virtual function void fa();\n"
      "endclass\n"
      "interface class B extends A;\n"
      "  pure virtual function void fb();\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n"));
}

// §8.26.2: Interface class cannot use implements.
TEST(ElabA8262, InterfaceImplementsError) {
  EXPECT_FALSE(ElabOk(
      "interface class A;\n"
      "  pure virtual function void fa();\n"
      "endclass\n"
      "interface class B implements A;\n"
      "  pure virtual function void fb();\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n"));
}

// §8.26.2: Interface class cannot extend a regular class.
TEST(ElabA8262, InterfaceExtendsClassError) {
  EXPECT_FALSE(ElabOk(
      "class Base;\n"
      "endclass\n"
      "interface class IC extends Base;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n"));
}

// §8.26.2: Regular class cannot extend an interface class.
TEST(ElabA8262, ClassExtendsInterfaceError) {
  EXPECT_FALSE(ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "class C extends IC;\n"
      "  virtual function void foo();\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n"));
}

// §8.26.2: Class implements interface class — OK.
TEST(ElabA8262, ClassImplementsInterfaceOk) {
  EXPECT_TRUE(ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "class C implements IC;\n"
      "  virtual function void foo();\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n"));
}

// §8.26.2: Class extends base and implements interface — OK.
TEST(ElabA8262, ClassExtendsAndImplementsOk) {
  EXPECT_TRUE(ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "class Base;\n"
      "endclass\n"
      "class Child extends Base implements IC;\n"
      "  virtual function void foo();\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n"));
}

// §8.26.2: Class implements multiple interfaces — OK.
TEST(ElabA8262, ClassImplementsMultipleOk) {
  EXPECT_TRUE(ElabOk(
      "interface class A;\n"
      "  pure virtual function void fa();\n"
      "endclass\n"
      "interface class B;\n"
      "  pure virtual function void fb();\n"
      "endclass\n"
      "class C implements A, B;\n"
      "  virtual function void fa();\n"
      "  endfunction\n"
      "  virtual function void fb();\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n"));
}

// §8.26.2: Non-abstract class missing implementation — error.
TEST(ElabA8262, ClassMissingImplementationError) {
  EXPECT_FALSE(ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "class C implements IC;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n"));
}

// §8.26.2: Virtual class partial implementation — OK (§8.26.7).
TEST(ElabA8262, VirtualClassPartialImplOk) {
  EXPECT_TRUE(ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "virtual class C implements IC;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n"));
}

}  // namespace
