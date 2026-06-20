#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(StaticMethodElaboration, StaticMethodThisError) {
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

TEST(StaticMethodElaboration, StaticMethodSuperError) {
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

TEST(StaticMethodElaboration, StaticMethodAccessingStaticPropertyOk) {
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

TEST(StaticMethodElaboration, NonStaticMethodThisOk) {
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

TEST(StaticMethodElaboration, StaticMethodNoThisSuperOk) {
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

TEST(StaticMethodElaboration, StaticMethodCallsStaticMethodOk) {
  EXPECT_TRUE(
      ElabOk("class Util;\n"
             "  static int count;\n"
             "  static function void inc();\n"
             "    count = count + 1;\n"
             "  endfunction\n"
             "  static function void inc_twice();\n"
             "    inc();\n"
             "    inc();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Util u;\n"
             "endmodule\n"));
}

TEST(StaticMethodElaboration, StaticMethodThisInConditionError) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  static function int check();\n"
             "    if (this.x > 0) return 1;\n"
             "    return 0;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(StaticMethodElaboration, StaticMethodThisInAssignmentError) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  static function void reset();\n"
             "    this.x = 0;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(StaticMethodElaboration, StaticTaskThisError) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  static task set_x();\n"
             "    this.x = 5;\n"
             "  endtask\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(StaticMethodElaboration, UnqualifiedNonStaticPropertyError) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  static function void f();\n"
             "    x = 5;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(StaticMethodElaboration, UnqualifiedNonStaticMethodCallError) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  function void helper(); endfunction\n"
             "  static function void f();\n"
             "    helper();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(StaticMethodElaboration, LocalShadowsNonStaticOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  static function void f();\n"
             "    int x;\n"
             "    x = 5;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(StaticMethodElaboration, ParamShadowsNonStaticOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  static function void f(int x);\n"
             "    x = 5;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(StaticMethodElaboration, StaticMethodThisInCallArgError) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  static function int id(int v);\n"
             "    return v;\n"
             "  endfunction\n"
             "  static function int bad();\n"
             "    return id(this.x);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

}  // namespace
