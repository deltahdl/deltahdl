#include <gtest/gtest.h>

#include <initializer_list>

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

TEST(ChainedConstructorElaboration,
     DefaultKeywordRulesAreReportedInEveryPlace) {
  ElabFixture f;
  ElabOk(
      "package pk;\n"
      "  class PQ; function new(int x = 1); endfunction endclass\n"
      "  class PB; local int m_id = 7; function new(int x = m_id); "
      "endfunction endclass\n"
      "  class P0; function new(default); endfunction endclass\n"
      "  class P1 extends PQ; function new(default, int x); endfunction "
      "endclass\n"
      "  class P2 extends PB; function new(default); endfunction endclass\n"
      "  class P3 extends PQ; function new(); super.new(default); "
      "endfunction endclass\n"
      "  class P4 extends PQ(default); function new(); endfunction "
      "endclass\n"
      "  class P5 extends PQ(3); function new(); super.new(3); endfunction "
      "endclass\n"
      "  class P6 extends PQ; function new(int y, default, int z); "
      "endfunction endclass\n"
      "endpackage\n"
      "class CQ; protected int p_id = 3; function new(int x = p_id); "
      "endfunction endclass\n"
      "class CL; local int m_id = 7; function new(int x = m_id + 1); "
      "endfunction endclass\n"
      "class C0; function new(default); endfunction endclass\n"
      "class C1 extends CQ; function new(default); endfunction endclass\n"
      "class C2 extends CL; function new(default); endfunction endclass\n"
      "class C3 extends CQ; function new(default, int x); endfunction "
      "endclass\n"
      "class E1 extends CQ; extern function new(default, int x); endclass\n"
      "function E1::new(default, int x); endfunction\n"
      "class E2; extern function new(default); endclass\n"
      "function E2::new(default); endfunction\n"
      "class E3 extends CQ; extern function new(default, int y); endclass\n"
      "function E3::new(default, int y); endfunction\n"
      "program p;\n"
      "  class G0; function new(default); endfunction endclass\n"
      "  class G2 extends CL; function new(default); endfunction endclass\n"
      "  class G3 extends CQ; function new(int y, default); endfunction "
      "endclass\n"
      "  G0 g0; G2 g2; G3 g3;\n"
      "endprogram\n"
      "interface ifc;\n"
      "  class I0; function new(default); endfunction endclass\n"
      "  class I1 extends CQ; function new(default, int x); endfunction "
      "endclass\n"
      "  class I3 extends CQ; function new(default, int y); endfunction "
      "endclass\n"
      "  I0 i0; I1 i1; I3 i3;\n"
      "endinterface\n"
      "module m;\n"
      "  class M0; function new(default); endfunction endclass\n"
      "  class M3 extends CQ; function new(); super.new(default); "
      "endfunction endclass\n"
      "  class M4 extends CQ(default); function new(); endfunction "
      "endclass\n"
      "  class M5 extends CQ(3); function new(); super.new(3); endfunction "
      "endclass\n"
      "  class M6 extends CQ(default); function new(default); endfunction "
      "endclass\n"
      "  class M7 extends CQ; function new(default); super.new(default); "
      "endfunction endclass\n"
      "  class M8 extends CQ(3); function new(); endfunction endclass\n"
      "  pk::P0 a0; pk::P1 a1; pk::P2 a2; pk::P3 a3; pk::P4 a4; pk::P5 a5;\n"
      "  pk::P6 a6; C0 c0; C1 c1; C2 c2; C3 c3; E1 e1; E2 e2; E3 e3;\n"
      "  M0 m0; M3 m3; M4 m4; M5 m5; M6 m6; M7 m7; M8 m8;\n"
      "  p pi(); ifc ii();\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {4, 14, 21, 25, 31, 37}) {
    EXPECT_TRUE(ReportedError(
        diags, "requires the class to extend a superclass", kLine, "8.17"))
        << kLine;
  }
  for (const int kLine : {5, 17, 19, 32}) {
    EXPECT_TRUE(ReportedError(
        diags, "shall not share a name with a superclass constructor argument",
        kLine, "8.17"))
        << kLine;
  }
  for (const int kLine : {6, 16, 26}) {
    EXPECT_TRUE(ReportedError(
        diags, "argument's default value refers to a local member", kLine,
        "8.17"))
        << kLine;
  }
  for (const int kLine : {7, 38}) {
    EXPECT_TRUE(ReportedError(diags,
                              "may be passed to super.new() only when the "
                              "constructor argument list uses the 'default' "
                              "keyword",
                              kLine, "8.17"))
        << kLine;
  }
  for (const int kLine : {8, 39}) {
    EXPECT_TRUE(ReportedError(diags,
                              "the extends specifier uses 'default', so the "
                              "constructor's argument list has to repeat "
                              "'default'",
                              kLine, "8.17"))
        << kLine;
  }
  for (const int kLine : {9, 40}) {
    EXPECT_TRUE(ReportedError(diags,
                              "constructor calls super.new() although the "
                              "extends specifier already supplies the "
                              "superclass constructor's arguments",
                              kLine, "8.17"))
        << kLine;
  }
  for (const int kLine : {10, 12, 13, 15, 22, 23, 27, 33, 41, 42, 43}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

}  // namespace
