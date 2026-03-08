#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §8.10: Static method with 'this' reference is illegal.
TEST(ElabA810, StaticMethodThisError) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  static function int get_x();\n"
             "    return this.x;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

// §8.10: Static method with 'super' reference is illegal.
TEST(ElabA810, StaticMethodSuperError) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  function void foo(); endfunction\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  static function void bar();\n"
             "    super.foo();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "endmodule\n"));
}

// §8.10: Static method accessing static property is legal.
TEST(ElabA810, StaticMethodAccessingStaticPropertyOk) {
  EXPECT_TRUE(
      ElabOk("class id;\n"
             "  static int current;\n"
             "  static function int next_id();\n"
             "    return current;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  id i;\n"
             "endmodule\n"));
}

// §8.10: Non-static method using 'this' is fine.
TEST(ElabA810, NonStaticMethodThisOk) {
  EXPECT_TRUE(
      ElabOk("class Demo;\n"
             "  int x;\n"
             "  function void set_x(int val);\n"
             "    this.x = val;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Demo d;\n"
             "endmodule\n"));
}

// §8.10: Static method with no this/super references is fine.
TEST(ElabA810, StaticMethodNoThisSuperOk) {
  EXPECT_TRUE(
      ElabOk("class Util;\n"
             "  static function int add(int a, int b);\n"
             "    return a + b;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Util u;\n"
             "endmodule\n"));
}

}  // namespace
