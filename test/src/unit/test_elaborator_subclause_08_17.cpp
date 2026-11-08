#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "constructor calls super.new() although the extends specifier already "
      "supplies the superclass constructor's arguments",
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "super.new() does not open the constructor, and no "
                            "executable statement may come before it",
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "super.new() does not open the constructor, and no "
                            "executable statement may come before it",
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "constructor calls super.new() although the extends specifier already "
      "supplies the superclass constructor's arguments",
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
                            "argument's default value refers to a local member",
                            7, "8.17"));
}

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
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "the extends specifier uses 'default', so the "
                    "constructor's argument list has to repeat 'default'",
                    6, "8.17"));
}

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "super.new() does not open the constructor, and no "
                            "executable statement may come before it",
                            7, "8.17"));
}

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "super.new() does not open the constructor, and no "
                            "executable statement may come before it",
                            7, "8.17"));
}

TEST(ChainedConstructorElaboration, SuperNewInAForkArmError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n"
      "class Child extends Base;\n"
      "  function new();\n"
      "    fork\n"
      "      super.new();\n"
      "    join_none\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Child c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "super.new() does not open the constructor, and no "
                            "executable statement may come before it",
                            7, "8.17"));
}

TEST(ChainedConstructorElaboration, SuperNewInAForStepError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n"
      "class Child extends Base;\n"
      "  function new();\n"
      "    for (int i = 0; i < 2; super.new()) ;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Child c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "super.new() does not open the constructor, and no "
                            "executable statement may come before it",
                            7, "8.17"));
}

TEST(ChainedConstructorElaboration, SuperNewInAnAssertionPassStmtError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n"
      "class Child extends Base;\n"
      "  function new();\n"
      "    assert (1) super.new();\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Child c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "super.new() does not open the constructor, and no "
                            "executable statement may come before it",
                            7, "8.17"));
}
TEST(ChainedConstructorElaboration, SuperNewInAnAssertionFailStmtError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n"
      "class Child extends Base;\n"
      "  function new();\n"
      "    assert (1) else super.new();\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Child c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "super.new() does not open the constructor, and no "
                            "executable statement may come before it",
                            7, "8.17"));
}

TEST(ChainedConstructorElaboration, SuperNewInARandcaseItemError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n"
      "class Child extends Base;\n"
      "  function new();\n"
      "    randcase\n"
      "      1 : super.new();\n"
      "    endcase\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Child c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "super.new() does not open the constructor, and no "
                            "executable statement may come before it",
                            7, "8.17"));
}

TEST(ChainedConstructorElaboration, SuperNewInARandsequenceCodeBlockError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n"
      "class Child extends Base;\n"
      "  function new();\n"
      "    randsequence(main)\n"
      "      main : { super.new(); };\n"
      "    endsequence\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Child c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "super.new() does not open the constructor, and no "
                            "executable statement may come before it",
                            7, "8.17"));
}

TEST(ChainedConstructorElaboration, SuperNewInAForkArmUnderAnIfError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n"
      "class Child extends Base;\n"
      "  function new();\n"
      "    if (1)\n"
      "      fork\n"
      "        super.new();\n"
      "      join_none\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Child c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "super.new() does not open the constructor, and no "
                            "executable statement may come before it",
                            7, "8.17"));
}
TEST(ChainedConstructorElaboration, SuperNewInAForStepUnderAnIfError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n"
      "class Child extends Base;\n"
      "  function new();\n"
      "    if (1)\n"
      "      for (int i = 0; i < 2; super.new()) ;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Child c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "super.new() does not open the constructor, and no "
                            "executable statement may come before it",
                            7, "8.17"));
}
TEST(ChainedConstructorElaboration,
     SuperNewInAnAssertionPassStmtUnderAnIfError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n"
      "class Child extends Base;\n"
      "  function new();\n"
      "    if (1)\n"
      "      assert (1) super.new();\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Child c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "super.new() does not open the constructor, and no "
                            "executable statement may come before it",
                            7, "8.17"));
}
TEST(ChainedConstructorElaboration,
     SuperNewInAnAssertionFailStmtUnderAnIfError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n"
      "class Child extends Base;\n"
      "  function new();\n"
      "    if (1)\n"
      "      assert (1) else super.new();\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Child c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "super.new() does not open the constructor, and no "
                            "executable statement may come before it",
                            7, "8.17"));
}
TEST(ChainedConstructorElaboration, SuperNewInARandcaseItemUnderAnIfError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n"
      "class Child extends Base;\n"
      "  function new();\n"
      "    if (1)\n"
      "      randcase\n"
      "        1 : super.new();\n"
      "      endcase\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Child c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "super.new() does not open the constructor, and no "
                            "executable statement may come before it",
                            7, "8.17"));
}
TEST(ChainedConstructorElaboration,
     SuperNewInARandsequenceCodeBlockUnderAnIfError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n"
      "class Child extends Base;\n"
      "  function new();\n"
      "    if (1)\n"
      "      randsequence(main)\n"
      "        main : { super.new(); };\n"
      "      endsequence\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Child c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "super.new() does not open the constructor, and no "
                            "executable statement may come before it",
                            7, "8.17"));
}

TEST(ChainedConstructorElaboration, SuperNewFirstInABeginEndBlockOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  function new();\n"
             "  endfunction\n"
             "endclass\n"
             "class Child extends Base;\n"
             "  int x;\n"
             "  function new();\n"
             "    begin\n"
             "      super.new();\n"
             "      x = 1;\n"
             "    end\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Child c;\n"
             "endmodule\n"));
}

TEST(ChainedConstructorElaboration, PackageClassSuperNewNotFirstIsAnError) {
  ElabFixture f;
  ElabOk(
      "package p;\n"
      "  class B; function new(int a = 0); endfunction endclass\n"
      "  class D extends B;\n"
      "    int x;\n"
      "    function new();\n"
      "      x = 1;\n"
      "      super.new(2);\n"
      "    endfunction\n"
      "  endclass\n"
      "endpackage\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "super.new() does not open the constructor, and no "
                            "executable statement may come before it",
                            7, "8.17"));
}

TEST(ChainedConstructorElaboration, ADeclarationAheadOfSuperNewIsNoStatement) {
  ElabFixture f;
  ElabOk(
      "class B; function new(int a = 0); endfunction endclass\n"
      "class D extends B;\n"
      "  int x;\n"
      "  function new();\n"
      "    int scratch;\n"
      "    super.new(1);\n"
      "  endfunction\n"
      "endclass\n"
      "class E extends B;\n"
      "  int x;\n"
      "  function new();\n"
      "    int scratch;\n"
      "    x = 1;\n"
      "    super.new(1);\n"
      "  endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  const char* const kMessage =
      "super.new() does not open the constructor, and no executable statement "
      "may come before it";
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kMessage, 6, "8.17"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, 14, "8.17"));
}

}  // namespace
