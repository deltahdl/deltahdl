#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ChainedConstructorElaboration, ExtendsArgsAndSuperNewError) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  function new(int x);\n"
             "  endfunction\n"
             "endclass\n"
             "class Child extends Base(5);\n"
             "  function new();\n"
             "    super.new(5);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Child c;\n"
             "endmodule\n"));
}

TEST(ChainedConstructorElaboration, ExtendsArgsNoSuperNewOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  function new(int x);\n"
             "  endfunction\n"
             "endclass\n"
             "class EtherPacket extends Base(5);\n"
             "endclass\n"
             "module m;\n"
             "  EtherPacket p;\n"
             "endmodule\n"));
}

TEST(ChainedConstructorElaboration, SuperNewInConstructorOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  function new();\n"
             "  endfunction\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  function new();\n"
             "    super.new();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "endmodule\n"));
}

TEST(ChainedConstructorElaboration, SuperNewNotFirstStatementError) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  function new();\n"
             "  endfunction\n"
             "endclass\n"
             "class Child extends Base;\n"
             "  int x;\n"
             "  function new();\n"
             "    x = 1;\n"
             "    super.new();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Child c;\n"
             "endmodule\n"));
}

TEST(ChainedConstructorElaboration, ImplicitSuperNewOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  function new();\n"
             "  endfunction\n"
             "endclass\n"
             "class Child extends Base;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  Child c;\n"
             "endmodule\n"));
}

TEST(ChainedConstructorElaboration, SuperNewWithArgsOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  int x;\n"
             "  function new(int v);\n"
             "    x = v;\n"
             "  endfunction\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  function new(int v);\n"
             "    super.new(v);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "endmodule\n"));
}

TEST(ChainedConstructorElaboration, SuperNewInsideIfBlockError) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  function new();\n"
             "  endfunction\n"
             "endclass\n"
             "class Child extends Base;\n"
             "  int x;\n"
             "  function new(int v);\n"
             "    if (v > 0) super.new();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Child c;\n"
             "endmodule\n"));
}

TEST(ChainedConstructorElaboration, ExtendsDefaultAndSuperNewError) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  function new(int x);\n"
             "  endfunction\n"
             "endclass\n"
             "class Child extends Base(default);\n"
             "  function new(default);\n"
             "    super.new(default);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Child c;\n"
             "endmodule\n"));
}

TEST(ChainedConstructorElaboration, ExtendsDefaultNoSuperNewOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  function new(int x);\n"
             "  endfunction\n"
             "endclass\n"
             "class Child extends Base(default);\n"
             "  function new(default);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Child c;\n"
             "endmodule\n"));
}

// §8.17: the 'default' keyword in a constructor argument list requires the
// class to be a subclass.
TEST(ChainedConstructorElaboration, DefaultArgInNonSubclassError) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  function new(default);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Base b;\n"
             "endmodule\n"));
}

// §8.17: a 'default'-expanded constructor argument list shall not declare an
// explicit argument whose name collides with a superclass constructor argument.
TEST(ChainedConstructorElaboration, DefaultArgNameCollidesWithSuperError) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  function new(int x);\n"
             "  endfunction\n"
             "endclass\n"
             "class Child extends Base;\n"
             "  function new(int x, default);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Child c;\n"
             "endmodule\n"));
}

// §8.17: a non-colliding explicit argument alongside 'default' is permitted.
TEST(ChainedConstructorElaboration, DefaultArgNoNameCollisionOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  function new(int x);\n"
             "  endfunction\n"
             "endclass\n"
             "class Child extends Base;\n"
             "  function new(int y, default);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Child c;\n"
             "endmodule\n"));
}

// §8.17: 'default' shall not be used when a superclass constructor argument's
// default value refers to a local member of the superclass.
TEST(ChainedConstructorElaboration, DefaultArgRefersToSuperLocalError) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  local int m_id = 7;\n"
             "  function new(int x = m_id);\n"
             "  endfunction\n"
             "endclass\n"
             "class Child extends Base;\n"
             "  function new(default);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Child c;\n"
             "endmodule\n"));
}

// §8.17: passing 'default' as the sole argument to super.new() is legal when
// the constructor's own argument list uses the 'default' keyword and the
// extends specifier carries no arguments of its own.
TEST(ChainedConstructorElaboration, SuperNewDefaultWithDefaultArgOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  function new(int x);\n"
             "  endfunction\n"
             "endclass\n"
             "class Child extends Base;\n"
             "  function new(default);\n"
             "    super.new(default);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Child c;\n"
             "endmodule\n"));
}

// §8.17: super.new(default) is only legal when the constructor argument list
// itself used the 'default' keyword.
TEST(ChainedConstructorElaboration, SuperNewDefaultWithoutDefaultArgError) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  function new(int x);\n"
             "  endfunction\n"
             "endclass\n"
             "class Child extends Base;\n"
             "  function new();\n"
             "    super.new(default);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Child c;\n"
             "endmodule\n"));
}

// §8.17: a subclass constructor whose extends specifier uses 'default' shall
// repeat the 'default' keyword in its own argument list.
TEST(ChainedConstructorElaboration, ExtendsDefaultUserCtorMissingDefaultError) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  function new(int x);\n"
             "  endfunction\n"
             "endclass\n"
             "class Child extends Base(default);\n"
             "  function new();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Child c;\n"
             "endmodule\n"));
}

// §8.17: super.new() shall be the first executable statement. A call reached
// only through a loop body is conditional on the loop running, so it can never
// be the unconditional first statement -- rejected. (Distinct control-flow
// position from the if-branch case.)
TEST(ChainedConstructorElaboration, SuperNewInLoopBodyError) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  function new();\n"
             "  endfunction\n"
             "endclass\n"
             "class Child extends Base;\n"
             "  function new();\n"
             "    for (int i = 0; i < 2; i++) super.new();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Child c;\n"
             "endmodule\n"));
}

// §8.17: a super.new() reached only through a case-item body is likewise
// conditional and thus never the first executable statement -- rejected.
TEST(ChainedConstructorElaboration, SuperNewInCaseItemError) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  function new();\n"
             "  endfunction\n"
             "endclass\n"
             "class Child extends Base;\n"
             "  function new(int sel);\n"
             "    case (sel)\n"
             "      0: super.new();\n"
             "    endcase\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Child c;\n"
             "endmodule\n"));
}

}  // namespace
