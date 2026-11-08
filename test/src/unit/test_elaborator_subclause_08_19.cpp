#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ConstantClassPropertyElaboration, GlobalConstantOk) {
  EXPECT_TRUE(
      ElabOk("class Jumbo_Packet;\n"
             "  const int max_size = 9 * 1024;\n"
             "endclass\n"
             "module m;\n"
             "  Jumbo_Packet p;\n"
             "endmodule\n"));
}

TEST(ConstantClassPropertyElaboration, StaticConstGlobalOk) {
  EXPECT_TRUE(
      ElabOk("class Config;\n"
             "  static const int VERSION = 3;\n"
             "endclass\n"
             "module m;\n"
             "  Config c;\n"
             "endmodule\n"));
}

TEST(ConstantClassPropertyElaboration, InstanceConstantOk) {
  EXPECT_TRUE(
      ElabOk("class Big_Packet;\n"
             "  const int size;\n"
             "  function new();\n"
             "    size = 4096;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Big_Packet p;\n"
             "endmodule\n"));
}

TEST(ConstantClassPropertyElaboration, InstanceConstStaticError) {
  ElabFixture f;
  ElabOk(
      "class Bad;\n"
      "  static const int size;\n"
      "endclass\n"
      "module m;\n"
      "  Bad b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "instance constant cannot be declared static", 2,
                            "8.19"));
}

TEST(ConstantClassPropertyElaboration, GlobalAndInstanceConstInSameClass) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  const int max_size = 1024;\n"
             "  const int size;\n"
             "  function new();\n"
             "    size = 512;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "endmodule\n"));
}

TEST(ConstantClassPropertyElaboration, MultipleInstanceConstantsOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  const int a;\n"
             "  const int b;\n"
             "  function new(int x, int y);\n"
             "    a = x;\n"
             "    b = y;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(ConstantClassPropertyElaboration, ConstWithLocalQualifierOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  local const int X = 10;\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(ConstantClassPropertyElaboration, ConstWithProtectedQualifierOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  protected const int Y = 20;\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(ConstantClassPropertyElaboration, InstanceConstInSubclass) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  const int id;\n"
             "  function new(int i);\n"
             "    id = i;\n"
             "  endfunction\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  function new();\n"
             "    super.new(99);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "endmodule\n"));
}

TEST(ConstantClassPropertyElaboration, GlobalConstAssignInConstructorError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  const int MAX = 100;\n"
      "  function new();\n"
      "    MAX = 200;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment to global constant", 4, "8.19"));
}

TEST(ConstantClassPropertyElaboration, GlobalConstAssignInMethodError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  const int MAX = 100;\n"
      "  function void reset();\n"
      "    MAX = 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment to global constant", 4, "8.19"));
}

TEST(ConstantClassPropertyElaboration, InstanceConstAssignInMethodError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  const int id;\n"
      "  function new();\n"
      "    id = 1;\n"
      "  endfunction\n"
      "  function void reset();\n"
      "    id = 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment to instance constant", 7, "8.19"));
}

TEST(ConstantClassPropertyElaboration, InstanceConstDoubleAssignInCtorError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  const int size;\n"
      "  function new();\n"
      "    size = 1;\n"
      "    size = 2;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "is assigned more than once in the constructor", 5,
                            "8.19"));
}

TEST(ConstantClassPropertyElaboration, InstanceConstBranchedSingleAssignOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  const int size;\n"
             "  function new(int sel);\n"
             "    if (sel)\n"
             "      size = 1;\n"
             "    else\n"
             "      size = 2;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(ConstantClassPropertyElaboration, InstanceConstAssignInTaskError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  const int id;\n"
      "  function new();\n"
      "    id = 1;\n"
      "  endfunction\n"
      "  task set_id();\n"
      "    id = 2;\n"
      "  endtask\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment to instance constant", 7, "8.19"));
}

TEST(ConstantClassPropertyElaboration, GlobalConstAssignInForkArmError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  const int MAX = 100;\n"
      "  task reset();\n"
      "    fork\n"
      "      MAX = 0;\n"
      "    join\n"
      "  endtask\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment to global constant", 5, "8.19"));
}

TEST(ConstantClassPropertyElaboration,
     GlobalConstAssignInForInitializationError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  const int MAX = 100;\n"
      "  task reset();\n"
      "    int i;\n"
      "    for (MAX = 0; i < 2; i = i + 1) ;\n"
      "  endtask\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment to global constant", 5, "8.19"));
}

TEST(ConstantClassPropertyElaboration, GlobalConstAssignInForStepError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  const int MAX = 100;\n"
      "  task reset();\n"
      "    int i;\n"
      "    for (i = 0; i < 2; MAX = 0) ;\n"
      "  endtask\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment to global constant", 5, "8.19"));
}

TEST(ConstantClassPropertyElaboration,
     GlobalConstAssignInAssertionPassStmtError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  const int MAX = 100;\n"
      "  task reset();\n"
      "    assert (1) MAX = 0;\n"
      "  endtask\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment to global constant", 4, "8.19"));
}

TEST(ConstantClassPropertyElaboration,
     GlobalConstAssignInAssertionFailStmtError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  const int MAX = 100;\n"
      "  task reset();\n"
      "    assert (1) else MAX = 0;\n"
      "  endtask\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment to global constant", 4, "8.19"));
}

TEST(ConstantClassPropertyElaboration, GlobalConstAssignInRandcaseItemError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  const int MAX = 100;\n"
      "  task reset();\n"
      "    randcase\n"
      "      1 : MAX = 0;\n"
      "    endcase\n"
      "  endtask\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment to global constant", 5, "8.19"));
}

TEST(ConstantClassPropertyElaboration,
     GlobalConstAssignInRandsequenceCodeBlockError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  const int MAX = 100;\n"
      "  task reset();\n"
      "    randsequence(main)\n"
      "      main : { MAX = 0; };\n"
      "    endsequence\n"
      "  endtask\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment to global constant", 5, "8.19"));
}

TEST(ConstantClassPropertyElaboration, ModuleClassGlobalConstAssignError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  class C;\n"
      "    const int k = 5;\n"
      "    function void f();\n"
      "      k = 6;\n"
      "    endfunction\n"
      "  endclass\n"
      "  C h;\n"
      "  initial begin h = new; h.f(); end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment to global constant 'k'", 5, "8.19"));
}

TEST(ConstantClassPropertyElaboration, PackageClassGlobalConstAssignError) {
  ElabFixture f;
  ElabOk(
      "package p;\n"
      "  class C;\n"
      "    const int k = 5;\n"
      "    function void f();\n"
      "      k = 6;\n"
      "    endfunction\n"
      "  endclass\n"
      "endpackage\n"
      "module m;\n"
      "  p::C h;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment to global constant 'k'", 5, "8.19"));
}

TEST(ConstantClassPropertyElaboration,
     ProgramClassInstanceConstAssignInMethodError) {
  ElabFixture f;
  ElabOk(
      "program pr;\n"
      "  class C;\n"
      "    const int id;\n"
      "    function new();\n"
      "      id = 1;\n"
      "    endfunction\n"
      "    function void reset();\n"
      "      id = 0;\n"
      "    endfunction\n"
      "  endclass\n"
      "endprogram\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment to instance constant 'id'", 8, "8.19"));
}

TEST(ConstantClassPropertyElaboration, InterfaceClassInstanceConstStaticError) {
  ElabFixture f;
  ElabOk(
      "interface ifc;\n"
      "  class C;\n"
      "    static const int size;\n"
      "  endclass\n"
      "endinterface\n"
      "module m;\n"
      "  ifc i();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "instance constant cannot be declared static", 3,
                            "8.19"));
}

TEST(ConstantClassPropertyElaboration, NestedClassGlobalConstAssignError) {
  ElabFixture f;
  ElabOk(
      "class Outer;\n"
      "  class Inner;\n"
      "    const int k = 5;\n"
      "    function void f();\n"
      "      k = 6;\n"
      "    endfunction\n"
      "  endclass\n"
      "endclass\n"
      "module m;\n"
      "  Outer o;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment to global constant 'k'", 5, "8.19"));
}

TEST(ConstantClassPropertyElaboration, ModuleClassInstanceConstInCtorOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  class C;\n"
             "    const int size;\n"
             "    function new();\n"
             "      size = 4096;\n"
             "    endfunction\n"
             "  endclass\n"
             "  C h;\n"
             "  initial h = new;\n"
             "endmodule\n"));
}

TEST(ConstantClassPropertyElaboration, GlobalConstAssignThroughThisError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  const int k = 5;\n"
      "  function void f();\n"
      "    this.k = 6;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C h;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment to global constant 'k'", 4, "8.19"));
}

TEST(ConstantClassPropertyElaboration,
     InstanceConstAssignThroughThisOutsideCtorError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  const int id;\n"
      "  function new();\n"
      "    this.id = 1;\n"
      "  endfunction\n"
      "  function void reset();\n"
      "    this.id = 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C h;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment to instance constant 'id'", 7, "8.19"));
}

TEST(ConstantClassPropertyElaboration, InstanceConstAssignThroughThisInCtorOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  const int id;\n"
             "  function new();\n"
             "    this.id = 1;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C h;\n"
             "  initial h = new;\n"
             "endmodule\n"));
}

TEST(ConstantClassPropertyElaboration,
     GlobalConstAssignThroughClassScopeError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  static const int k = 5;\n"
      "  static function void f();\n"
      "    C::k = 6;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment to global constant 'k'", 4, "8.19"));
}

TEST(ConstantClassPropertyElaboration, GlobalConstAssignThroughHandleError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  const int k = 5;\n"
      "endclass\n"
      "module m;\n"
      "  C h;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    h.k = 6;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment to global constant 'k'", 8, "8.19"));
}

TEST(ConstantClassPropertyElaboration, InstanceConstAssignThroughHandleError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  const int id;\n"
      "  function new();\n"
      "    id = 1;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    static C h = new;\n"
      "    h.id = 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment to instance constant 'id'", 10,
                            "8.19"));
}

TEST(ConstantClassPropertyElaboration,
     StaticGlobalConstAssignThroughClassScopeFromModuleError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  static const int k = 5;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    C::k = 6;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment to global constant 'k'", 6, "8.19"));
}

TEST(ConstantClassPropertyElaboration, NonConstPropertyAssignThroughHandleOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  const int k = 5;\n"
             "  int v;\n"
             "endclass\n"
             "module m;\n"
             "  C h;\n"
             "  initial begin\n"
             "    h = new;\n"
             "    h.v = h.k;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ConstantClassPropertyElaboration,
     InheritedGlobalConstAssignInDerivedMethodError) {
  ElabFixture f;
  ElabOk(
      "class B;\n"
      "  const int k = 5;\n"
      "endclass\n"
      "class D extends B;\n"
      "  function void f();\n"
      "    k = 6;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  D h;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment to global constant 'k'", 6, "8.19"));
}

TEST(ConstantClassPropertyElaboration,
     InheritedInstanceConstAssignInDerivedCtorError) {
  ElabFixture f;
  ElabOk(
      "class B;\n"
      "  const int id;\n"
      "  function new();\n"
      "    id = 1;\n"
      "  endfunction\n"
      "endclass\n"
      "class D extends B;\n"
      "  function new();\n"
      "    super.new();\n"
      "    id = 2;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  D h;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment to instance constant 'id'", 10,
                            "8.19"));
}

TEST(ConstantClassPropertyElaboration, ShadowingPropertyOfInheritedConstOk) {
  EXPECT_TRUE(
      ElabOk("class B;\n"
             "  const int k = 5;\n"
             "endclass\n"
             "class D extends B;\n"
             "  int k;\n"
             "  function void f();\n"
             "    k = 6;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  D h;\n"
             "endmodule\n"));
}

TEST(ConstantClassPropertyElaboration,
     GlobalConstAssignThroughFormalInOtherClassMethodError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  const int k = 5;\n"
      "endclass\n"
      "class E;\n"
      "  function void g(C h);\n"
      "    h.k = 6;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  E e;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment to global constant 'k'", 6, "8.19"));
}

TEST(ConstantClassPropertyElaboration,
     GlobalConstAssignThroughPropertyHandleInOtherClassMethodError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  const int k = 5;\n"
      "endclass\n"
      "class E;\n"
      "  C h;\n"
      "  function void g();\n"
      "    h.k = 6;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  E e;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment to global constant 'k'", 7, "8.19"));
}

TEST(ConstantClassPropertyElaboration,
     GlobalConstAssignThroughFormalInModuleTaskError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  const int k = 5;\n"
      "endclass\n"
      "module m;\n"
      "  task t(C h);\n"
      "    h.k = 6;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment to global constant 'k'", 6, "8.19"));
}

TEST(ConstantClassPropertyElaboration,
     InstanceConstAssignThroughLocalInModuleFunctionError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  const int id;\n"
      "  function new();\n"
      "    id = 1;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  function void f();\n"
      "    static C h = new;\n"
      "    h.id = 2;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment to instance constant 'id'", 10,
                            "8.19"));
}

}  // namespace
