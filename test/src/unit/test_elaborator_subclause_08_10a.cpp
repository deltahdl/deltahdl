#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

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

TEST(StaticMethodElaboration, NonStaticPropertyWrittenInAForkArmIsReported) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  static task t();\n"
      "    fork\n"
      "      x = 5;\n"
      "    join\n"
      "  endtask\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "static method shall not access non-static members",
                            3, "8.10"));
}

TEST(StaticMethodElaboration, LocalDeclaredInAForkArmShadowsTheProperty) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  static task t();\n"
             "    fork\n"
             "      int x;\n"
             "      x = 5;\n"
             "    join\n"
             "  endtask\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(StaticMethodElaboration,
     NonStaticPropertyWrittenInAForInitializationIsReported) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  static task t();\n"
      "    int i;\n"
      "    for (x = 0; i < 2; i = i + 1) ;\n"
      "  endtask\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "static method shall not access non-static members",
                            3, "8.10"));
}

TEST(StaticMethodElaboration, NonStaticPropertyWrittenInAForStepIsReported) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  static task t();\n"
      "    int i;\n"
      "    for (i = 0; i < 2; x = x + 1) ;\n"
      "  endtask\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "static method shall not access non-static members",
                            3, "8.10"));
}

TEST(StaticMethodElaboration,
     NonStaticPropertyWrittenInAnAssertionPassStmtIsReported) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  static task t();\n"
      "    assert (1) x = 5;\n"
      "  endtask\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "static method shall not access non-static members",
                            3, "8.10"));
}

TEST(StaticMethodElaboration,
     LocalDeclaredInAnAssertionPassStmtShadowsTheProperty) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  static task t();\n"
             "    assert (1) begin\n"
             "      int x;\n"
             "      x = 5;\n"
             "    end\n"
             "  endtask\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(StaticMethodElaboration,
     NonStaticPropertyWrittenInAnAssertionFailStmtIsReported) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  static task t();\n"
      "    assert (1) else x = 5;\n"
      "  endtask\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "static method shall not access non-static members",
                            3, "8.10"));
}

TEST(StaticMethodElaboration,
     LocalDeclaredInAnAssertionFailStmtShadowsTheProperty) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  static task t();\n"
             "    assert (1) else begin\n"
             "      int x;\n"
             "      x = 5;\n"
             "    end\n"
             "  endtask\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(StaticMethodElaboration,
     NonStaticPropertyWrittenInARandcaseItemIsReported) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  static task t();\n"
      "    randcase\n"
      "      1 : x = 5;\n"
      "    endcase\n"
      "  endtask\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "static method shall not access non-static members",
                            3, "8.10"));
}

TEST(StaticMethodElaboration, LocalDeclaredInARandcaseItemShadowsTheProperty) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  static task t();\n"
             "    randcase\n"
             "      1 : begin\n"
             "        int x;\n"
             "        x = 5;\n"
             "      end\n"
             "    endcase\n"
             "  endtask\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(StaticMethodElaboration,
     NonStaticPropertyWrittenInARandsequenceCodeBlockIsReported) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  static task t();\n"
      "    randsequence(main)\n"
      "      main : { x = 5; };\n"
      "    endsequence\n"
      "  endtask\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "static method shall not access non-static members",
                            3, "8.10"));
}

TEST(StaticMethodElaboration,
     LocalDeclaredInARandsequenceCodeBlockShadowsTheProperty) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  static task t();\n"
             "    randsequence(main)\n"
             "      main : { int x; x = 5; };\n"
             "    endsequence\n"
             "  endtask\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(StaticMethodElaboration,
     NonStaticPropertyWrittenInARandsequenceWeightCodeBlockIsReported) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  static task t();\n"
      "    randsequence(main)\n"
      "      main : alt := 5 { x = 5; };\n"
      "      alt : { ; };\n"
      "    endsequence\n"
      "  endtask\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "static method shall not access non-static members",
                            3, "8.10"));
}

TEST(StaticMethodElaboration,
     LocalDeclaredInARandsequenceWeightCodeBlockShadowsTheProperty) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  static task t();\n"
             "    randsequence(main)\n"
             "      main : alt := 5 { int x; x = 5; };\n"
             "      alt : { ; };\n"
             "    endsequence\n"
             "  endtask\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(StaticMethodElaboration, ForHeaderControlVariableShadowsTheProperty) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int i;\n"
             "  static function void f();\n"
             "    int x;\n"
             "    for (int i = 0; i < 2; i = i + 1) x = i;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(StaticMethodElaboration, UntypedForHeaderVariableIsStillTheProperty) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int i;\n"
      "  static function void f();\n"
      "    int x;\n"
      "    for (i = 0; i < 2; i = i + 1) x = i;\n"
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

TEST(StaticMethodElaboration,
     ForHeaderControlVariableIsOutOfScopeAfterTheLoop) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int i;\n"
      "  static function void f();\n"
      "    int x;\n"
      "    for (int i = 0; i < 2; i = i + 1) x = 0;\n"
      "    x = i;\n"
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

TEST(StaticMethodElaboration, BlockLocalIsOutOfScopeAfterTheBlock) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int i;\n"
      "  static function void f();\n"
      "    int x;\n"
      "    begin : b\n"
      "      int i;\n"
      "      i = 1;\n"
      "    end\n"
      "    x = i;\n"
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

TEST(StaticMethodElaboration, BlockLocalShadowsThePropertyInANestedBlock) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int i;\n"
             "  static function void f();\n"
             "    begin\n"
             "      int i;\n"
             "      begin\n"
             "        i = 1;\n"
             "      end\n"
             "    end\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(StaticMethodClassScopeAccess,
     AnotherClassesStaticMethodCalledThroughItsScopeIsAccepted) {
  EXPECT_TRUE(
      ElabOk("class Registry;\n"
             "  static function int get();\n"
             "    return 1;\n"
             "  endfunction\n"
             "endclass\n"
             "class C;\n"
             "  virtual function int get(int key);\n"
             "    return key;\n"
             "  endfunction\n"
             "  static function int get_type();\n"
             "    return Registry::get();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(StaticMethodClassScopeAccess,
     AStaticMethodOfATypedefSpecializationIsAccepted) {
  EXPECT_TRUE(
      ElabOk("class Registry #(type T = int);\n"
             "  static function int get();\n"
             "    return 1;\n"
             "  endfunction\n"
             "endclass\n"
             "class C #(type KEY = int);\n"
             "  typedef Registry #(KEY) type_id;\n"
             "  virtual function int get(KEY key);\n"
             "    return key;\n"
             "  endfunction\n"
             "  static function int get_type();\n"
             "    return type_id::get();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C #(int) c;\n"
             "endmodule\n"));
}

TEST(StaticMethodClassScopeAccess, TheOwnNonStaticMethodCalledBareIsReported) {
  ElabFixture f;
  ElabOk(
      "class Registry;\n"
      "  static function int get();\n"
      "    return 1;\n"
      "  endfunction\n"
      "endclass\n"
      "class C;\n"
      "  virtual function int get(int key);\n"
      "    return key;\n"
      "  endfunction\n"
      "  static function int get_type();\n"
      "    return get(1);\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "static method shall not access non-static members",
                            10, "8.10"));
}

TEST(StaticMethodElaboration, StaticMethodThisInAnInitializerError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int k;\n"
      "  static function int f();\n"
      "    int x = this.k;\n"
      "    return x;\n"
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

}  // namespace
