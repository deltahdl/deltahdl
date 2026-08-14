#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// The report stands at the method's own declaration rather than at the
// statement holding 'this', because §8.10's rule is about the method: the
// elaborator scans a static method's body and reports the method once.
TEST(StaticMethodElaboration, StaticMethodThisError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  static function int get_x();\n"
      "    return this.x;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'this' and 'super' shall not be used in a static method", 3, "8.10"));
}

TEST(StaticMethodElaboration, StaticMethodSuperError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  function void foo(); endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  static function void bar();\n"
      "    super.foo();\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Derived d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'this' and 'super' shall not be used in a static method", 5, "8.10"));
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
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  static function int check();\n"
      "    if (this.x > 0) return 1;\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'this' and 'super' shall not be used in a static method", 3, "8.10"));
}

TEST(StaticMethodElaboration, StaticMethodThisInAssignmentError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  static function void reset();\n"
      "    this.x = 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'this' and 'super' shall not be used in a static method", 3, "8.10"));
}

TEST(StaticMethodElaboration, StaticTaskThisError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  static task set_x();\n"
      "    this.x = 5;\n"
      "  endtask\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'this' and 'super' shall not be used in a static method", 3, "8.10"));
}

TEST(StaticMethodElaboration, UnqualifiedNonStaticPropertyError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  static function void f();\n"
      "    x = 5;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "static method shall not access non-static members",
                            3, "8.10"));
}

TEST(StaticMethodElaboration, UnqualifiedNonStaticMethodCallError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  function void helper(); endfunction\n"
      "  static function void f();\n"
      "    helper();\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "static method shall not access non-static members",
                            3, "8.10"));
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

// The line names which of the two static methods broke the rule: id is clean
// and bad is not, so the report stands at bad's declaration and a test naming
// line 3 would be answering for a method the source never faulted.
TEST(StaticMethodElaboration, StaticMethodThisInCallArgError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
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
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'this' and 'super' shall not be used in a static method", 6, "8.10"));
}

}  // namespace
