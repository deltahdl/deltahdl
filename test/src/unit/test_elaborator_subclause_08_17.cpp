#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// The report stands at the constructor's `function` keyword rather than at the
// super.new() call, because ValidateOneClassChainingCtor in
// src/elaborator/elaborator_validate_class_members.cpp passes
// ctor->method->loc.
TEST(ChainedConstructorElaboration, ExtendsArgsAndSuperNewError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
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
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "constructor shall not contain super.new() when "
                            "extends specifier has arguments",
                            6, "8.17"));
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

// ReportSequentialSuperNew reports at the offending call's own line, which is
// the second statement of the constructor body.
TEST(ChainedConstructorElaboration, SuperNewNotFirstStatementError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
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
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "super.new() shall be the first executable statement in the constructor",
      9, "8.17"));
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

// ReportGuardedSuperNew reports at the top-level statement that encloses the
// guarded call, so the line is the `if` rather than the super.new() it guards.
TEST(ChainedConstructorElaboration, SuperNewInsideIfBlockError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
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
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "super.new() shall be the first executable statement in the constructor",
      8, "8.17"));
}

TEST(ChainedConstructorElaboration, ExtendsDefaultAndSuperNewError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
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
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "constructor shall not contain super.new() when "
                            "extends specifier has arguments",
                            6, "8.17"));
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
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  function new(default);\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Base b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "requires the class to extend a superclass", 2,
                            "8.17"));
}

// §8.17: a 'default'-expanded constructor argument list shall not declare an
// explicit argument whose name collides with a superclass constructor argument.
// The message names the colliding argument, so the fragment asserted is the
// part of the sentence the emission site writes down.
TEST(ChainedConstructorElaboration, DefaultArgNameCollidesWithSuperError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  function new(int x);\n"
      "  endfunction\n"
      "endclass\n"
      "class Child extends Base;\n"
      "  function new(int x, default);\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Child c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "shall not share a name with a superclass constructor argument", 6,
      "8.17"));
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
// default value refers to a local member of the superclass. The report stands
// at the subclass constructor, which is the declaration that used 'default',
// rather than at the superclass argument whose default value it names.
TEST(ChainedConstructorElaboration, DefaultArgRefersToSuperLocalError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
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
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "argument default value refers to a local member",
                            7, "8.17"));
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
  ElabFixture f;
  ElabOk(
      "class Base;\n"
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
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "may be passed to super.new() only when the "
                            "constructor argument list uses the 'default' "
                            "keyword",
                            7, "8.17"));
}

// §8.17: a subclass constructor whose extends specifier uses 'default' shall
// repeat the 'default' keyword in its own argument list.
TEST(ChainedConstructorElaboration, ExtendsDefaultUserCtorMissingDefaultError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  function new(int x);\n"
      "  endfunction\n"
      "endclass\n"
      "class Child extends Base(default);\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Child c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "constructor argument list shall contain 'default' "
                            "when the extends specifier uses the 'default' "
                            "keyword",
                            6, "8.17"));
}

// §8.17: super.new() shall be the first executable statement. A call reached
// only through a loop body is conditional on the loop running, so it can never
// be the unconditional first statement -- rejected. (Distinct control-flow
// position from the if-branch case.)
TEST(ChainedConstructorElaboration, SuperNewInLoopBodyError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
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
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "super.new() shall be the first executable statement in the constructor",
      7, "8.17"));
}

// §8.17: a super.new() reached only through a case-item body is likewise
// conditional and thus never the first executable statement -- rejected. The
// report stands at the `case` keyword, which is the top-level statement that
// encloses the call.
TEST(ChainedConstructorElaboration, SuperNewInCaseItemError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
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
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "super.new() shall be the first executable statement in the constructor",
      7, "8.17"));
}

}  // namespace
