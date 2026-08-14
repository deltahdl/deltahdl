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

// An initial block is not a class method at all, so what the elaborator
// enforces here is §8.11's rule that 'this' is confined to a non-static class
// method rather than §8.15's about a base class. The report stands at the
// `initial` keyword, since it is the procedure that is judged.
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
      "'this' shall only be used within non-static class methods", 2, "8.11"));
}

// Derived does extend Base, so §8.15 has nothing to say about this super; what
// it breaks is §8.10's rule that a static method references neither 'this' nor
// 'super'. That is the distinction SuperOutsideASubclassNames8_15 below turns
// on, and naming the subclause is what keeps the two apart.
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

// §8.15: "The super keyword is used from within a derived class to refer to
// members, class value parameters, or local value parameters of the base
// class." A class that extends nothing has no base class for super to name.
// The subclause on the report is what tells this rejection from §8.10's rule
// about super in a static method, which the same keyword in a different
// position breaches.
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

// §8.15 requires super.new to be the first statement executed in a
// constructor. A constructor whose super.new call is preceded by another
// statement violates the rule and must fail elaboration. The report the
// elaborator emits for it names §8.17, which is where the constructor's own
// subclause states the ordering, and it stands at the misplaced super.new()
// call rather than at the constructor.
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "super.new() shall be the first executable statement in the constructor",
      9, "8.17"));
}

// The same constructor is legal when super.new leads the body, confirming the
// ordering check only rejects the misplaced case.
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

// §8.15 requires super.new to be the first statement *executed*. A super.new
// call nested inside a conditional can never satisfy that: the branch condition
// executes before it. This covers the control-flow input form of the rule,
// which travels a different validation path than a merely out-of-order
// sequential call, so it is rejected at elaboration. The report stands at the
// `if` rather than at the super.new() inside it, because it is the guarding
// statement that makes the call unreachable as the first one, and it names
// §8.17 as the misplaced sequential call above does.
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "super.new() shall be the first executable statement in the constructor",
      8, "8.17"));
}

// §8.15 states that an expression reaching a base class value parameter
// through super is not a constant expression. A static variable initializer
// requires a constant expression, so initializing one from super.P (where P
// is the base's value parameter) must be rejected at elaboration. The super
// access is legal here because the enclosing method is a non-static method of
// a derived class. The report stands at the super keyword, which is where the
// member access the rule names begins.
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

// §8.15 names both a value parameter and a local value parameter as the kinds
// of parameter whose super-qualified access is non-constant. The test above
// exercises the value-parameter form; this one covers the local value
// parameter (a localparam declared in the base class, per §6.20.4). Reaching it
// through super in a static-variable initializer, which requires a constant
// expression, must therefore also be rejected at elaboration. The super access
// itself is legal because f is a non-static method of a derived class. The
// message names the kind, which is what tells this rejection from the one
// above.
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

// §8.15 states the rule for the expression, wherever it stands, so a report
// wired into the static-variable initializer alone leaves it unenforced
// everywhere else. §7.4.2 requires a fixed-size unpacked dimension to be a
// constant expression, which is a second such context and reaches the super
// access through a different field of the declaration than the initializer
// does.
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

// §8.15's first sentence makes super the way to reach a base class value
// parameter, and only its last sentence bars the reach from a constant
// expression. Returning the parameter's value from a method requires no
// constant, so the same access that the tests above reject is accepted here.
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

// Contrast control: the same static initializer context accepts a genuine
// constant, confirming the rejection above is caused by the super access
// being non-constant rather than by the static declaration itself.
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

}  // namespace
