#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(SuperElaboration, SuperInDerivedMethodOk) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  integer value;\n"
             "  function integer delay();\n"
             "    delay = value * value;\n"
             "  endfunction\n"
             "endclass\n"
             "class LinkedPacket extends Packet;\n"
             "  integer value;\n"
             "  function integer delay();\n"
             "    delay = super.delay() + value * super.value;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  LinkedPacket lp;\n"
             "endmodule\n"));
}

TEST(SuperElaboration, SuperInModuleBlockError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  initial begin\n"
      "    automatic int x;\n"
      "    x = super.val;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'this' has no object to refer to outside a non-static class method", 2,
      "8.11"));
}

TEST(SuperElaboration, SuperInStaticMethodError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  int x;\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  static function int get_x();\n"
      "    return super.x;\n"
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

TEST(SuperElaboration, SuperOutsideASubclassNames8_15) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  int x;\n"
      "  function int get();\n"
      "    return super.x;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Base b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'super' shall only be used in a derived class", 3,
                            "8.15"));
}

TEST(SuperElaboration, SuperAccessInheritedMemberOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  int x;\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  function int get_x();\n"
             "    return super.x;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "endmodule\n"));
}

TEST(SuperElaboration, SuperPropertyWriteInDerivedOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  int x;\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  int x;\n"
             "  function void set();\n"
             "    super.x = 10;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "endmodule\n"));
}

TEST(SuperElaboration, SuperNewMustBeFirstStatementError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  int y;\n"
      "  function new();\n"
      "    y = 1;\n"
      "    super.new();\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Derived d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "super.new() does not open the constructor, and no "
                            "executable statement may come before it",
                            9, "8.17"));
}

TEST(SuperElaboration, SuperNewFirstStatementOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  function new();\n"
             "  endfunction\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  int y;\n"
             "  function new();\n"
             "    super.new();\n"
             "    y = 1;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "endmodule\n"));
}

TEST(SuperElaboration, SuperNewInsideConditionalError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  int y;\n"
      "  function new();\n"
      "    if (y == 0) super.new();\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Derived d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "super.new() does not open the constructor, and no "
                            "executable statement may come before it",
                            8, "8.17"));
}

TEST(SuperElaboration, SuperValueParamNotConstantError) {
  ElabFixture f;
  ElabOk(
      "class Base #(parameter int P = 4);\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  function int f();\n"
      "    static int s = super.P;\n"
      "    return s;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Derived d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "expression using 'super' to access base class "
                            "value parameter 'P' is not a constant expression",
                            5, "8.15"));
}

TEST(SuperElaboration, SuperLocalValueParamNotConstantError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  localparam int LP = 4;\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  function int f();\n"
      "    static int s = super.LP;\n"
      "    return s;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Derived d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "expression using 'super' to access base class local value "
                    "parameter 'LP' is not a constant expression",
                    6, "8.15"));
}

TEST(SuperElaboration, SuperValueParamInUnpackedDimensionNames8_15) {
  ElabFixture f;
  ElabOk(
      "class Base #(parameter int P = 4);\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  function int f();\n"
      "    int a[super.P];\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Derived d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "expression using 'super' to access base class "
                            "value parameter 'P' is not a constant expression",
                            5, "8.15"));
}

TEST(SuperElaboration, SuperValueParamOutsideConstantContextOk) {
  EXPECT_TRUE(
      ElabOk("class Base #(parameter int P = 4);\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  function int get_p();\n"
             "    return super.P;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "endmodule\n"));
}

TEST(SuperElaboration, StaticInitConstantOk) {
  EXPECT_TRUE(
      ElabOk("class Base #(parameter int P = 4);\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  function int f();\n"
             "    static int s = 4;\n"
             "    return s;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "endmodule\n"));
}

TEST(SuperElaboration, SuperValueParamInAForkArmDeclarationNames8_15) {
  ElabFixture f;
  ElabOk(
      "class Base #(parameter int P = 4);\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  function int f();\n"
      "    fork\n"
      "      int a[super.P];\n"
      "    join_none\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Derived d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "expression using 'super' to access base class "
                            "value parameter 'P' is not a constant expression",
                            6, "8.15"));
}

TEST(SuperElaboration, SuperValueParamInAnAssertionPassStmtNames8_15) {
  ElabFixture f;
  ElabOk(
      "class Base #(parameter int P = 4);\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  function int f();\n"
      "    assert (1) begin\n"
      "      int a[super.P];\n"
      "    end\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Derived d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "expression using 'super' to access base class "
                            "value parameter 'P' is not a constant expression",
                            6, "8.15"));
}

TEST(SuperElaboration, SuperValueParamInAnAssertionFailStmtNames8_15) {
  ElabFixture f;
  ElabOk(
      "class Base #(parameter int P = 4);\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  function int f();\n"
      "    assert (1) else begin\n"
      "      int a[super.P];\n"
      "    end\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Derived d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "expression using 'super' to access base class "
                            "value parameter 'P' is not a constant expression",
                            6, "8.15"));
}

TEST(SuperElaboration, SuperValueParamInARandcaseItemNames8_15) {
  ElabFixture f;
  ElabOk(
      "class Base #(parameter int P = 4);\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  function int f();\n"
      "    randcase\n"
      "      1 : begin\n"
      "        int a[super.P];\n"
      "      end\n"
      "    endcase\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Derived d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "expression using 'super' to access base class "
                            "value parameter 'P' is not a constant expression",
                            7, "8.15"));
}

TEST(SuperElaboration, SuperValueParamInARandsequenceCodeBlockNames8_15) {
  ElabFixture f;
  ElabOk(
      "class Base #(parameter int P = 4);\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  function int f();\n"
      "    randsequence(main)\n"
      "      main : { int a[super.P]; };\n"
      "    endsequence\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Derived d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "expression using 'super' to access base class "
                            "value parameter 'P' is not a constant expression",
                            6, "8.15"));
}

TEST(SuperElaboration, SuperValueParamInARandsequenceWeightCodeBlockNames8_15) {
  ElabFixture f;
  ElabOk(
      "class Base #(parameter int P = 4);\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  function int f();\n"
      "    randsequence(main)\n"
      "      main : alt := 5 { int a[super.P]; };\n"
      "      alt : { ; };\n"
      "    endsequence\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Derived d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "expression using 'super' to access base class "
                            "value parameter 'P' is not a constant expression",
                            6, "8.15"));
}

TEST(SuperElaboration, SuperInAForkArmOutsideASubclassNames8_15) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  int x;\n"
      "  int i;\n"
      "  function void f();\n"
      "    fork\n"
      "      x = super.x;\n"
      "    join_none\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Base b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'super' shall only be used in a derived class", 4,
                            "8.15"));
}

TEST(SuperElaboration, SuperInAForInitializationOutsideASubclassNames8_15) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  int x;\n"
      "  int i;\n"
      "  function void f();\n"
      "    for (i = super.x; i < 2; i = i + 1) ;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Base b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'super' shall only be used in a derived class", 4,
                            "8.15"));
}

TEST(SuperElaboration, SuperInAForStepOutsideASubclassNames8_15) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  int x;\n"
      "  int i;\n"
      "  function void f();\n"
      "    for (i = 0; i < 2; i = super.x) ;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Base b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'super' shall only be used in a derived class", 4,
                            "8.15"));
}

TEST(SuperElaboration, SuperInAnAssertionPassStmtOutsideASubclassNames8_15) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  int x;\n"
      "  int i;\n"
      "  function void f();\n"
      "    assert (1) x = super.x;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Base b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'super' shall only be used in a derived class", 4,
                            "8.15"));
}
TEST(SuperElaboration, SuperInAnAssertionFailStmtOutsideASubclassNames8_15) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  int x;\n"
      "  int i;\n"
      "  function void f();\n"
      "    assert (1) else x = super.x;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Base b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'super' shall only be used in a derived class", 4,
                            "8.15"));
}

TEST(SuperElaboration, SuperInARandcaseItemOutsideASubclassNames8_15) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  int x;\n"
      "  int i;\n"
      "  function void f();\n"
      "    randcase\n"
      "      1 : x = super.x;\n"
      "    endcase\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Base b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'super' shall only be used in a derived class", 4,
                            "8.15"));
}

TEST(SuperElaboration, SuperInARandsequenceCodeBlockOutsideASubclassNames8_15) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  int x;\n"
      "  int i;\n"
      "  function void f();\n"
      "    randsequence(main)\n"
      "      main : { x = super.x; };\n"
      "    endsequence\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Base b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'super' shall only be used in a derived class", 4,
                            "8.15"));
}

TEST(SuperElaboration, SuperInAModuleClassWithNoBaseIsAnError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  class C;\n"
      "    int k;\n"
      "    function void g(); super.k = 1; endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'super' shall only be used in a derived class", 4,
                            "8.15"));
}

}  // namespace
