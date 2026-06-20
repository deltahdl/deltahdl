#include "fixture_elaborator.h"

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
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  initial begin\n"
             "    automatic int x;\n"
             "    x = super.val;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(SuperElaboration, SuperInStaticMethodError) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  int x;\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  static function int get_x();\n"
             "    return super.x;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "endmodule\n"));
}

TEST(SuperElaboration, SuperInNonDerivedClassError) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  int x;\n"
             "  function int get();\n"
             "    return super.x;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Base b;\n"
             "endmodule\n"));
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
// statement violates the rule and must fail elaboration.
TEST(SuperElaboration, SuperNewMustBeFirstStatementError) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
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
             "endmodule\n"));
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

// §8.15 states that an expression reaching a base class value parameter
// through super is not a constant expression. A static variable initializer
// requires a constant expression, so initializing one from super.P (where P
// is the base's value parameter) must be rejected at elaboration. The super
// access is legal here because the enclosing method is a non-static method of
// a derived class.
TEST(SuperElaboration, SuperValueParamNotConstantError) {
  EXPECT_FALSE(
      ElabOk("class Base #(parameter int P = 4);\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  function int f();\n"
             "    static int s = super.P;\n"
             "    return s;\n"
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
