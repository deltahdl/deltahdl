#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class ScopesOfARun : public VpiDesignRun {};

TEST_F(ScopesOfARun, AnInternalScopeReachesTheScopeHoldingIt) {
  Run("module sub; endmodule\n"
      "module top;\n"
      "  task t; endtask\n"
      "  function int f; return 1; endfunction\n"
      "  sub u ();\n"
      "endmodule\n");
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiScope, Named(vpiTaskFunc, top, "t"))),
            VpiObjectOf(top));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiScope, Named(vpiTaskFunc, top, "f"))),
            VpiObjectOf(top));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiScope, By("top.u"))), VpiObjectOf(top));
  EXPECT_EQ(vpi_handle(vpiScope, top), nullptr);
}

TEST_F(ScopesOfARun, AnArrayOfVirtualInterfacesYieldsEachElement) {
  Run("interface ifc; endinterface\n"
      "module top;\n"
      "  ifc i ();\n"
      "  virtual ifc v16;\n"
      "  virtual ifc v32[1:4];\n"
      "endmodule\n");
  EXPECT_EQ(NamesOf(vpiVirtualInterfaceVar, By("top")),
            (std::vector<std::string>{"v16", "v32[1]", "v32[2]", "v32[3]",
                                      "v32[4]"}));
}

TEST_F(ScopesOfARun, ATaskReachesTheStatementOfItsBody) {
  Run("module top;\n"
      "  int y;\n"
      "  task none; endtask\n"
      "  task one; y = 1; endtask\n"
      "  task two; int z; z = 2; y = z; endtask\n"
      "endmodule\n");
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  EXPECT_EQ(vpi_handle(vpiStmt, Named(vpiTaskFunc, top, "none")), nullptr);
  vpiHandle one = vpi_handle(vpiStmt, Named(vpiTaskFunc, top, "one"));
  ASSERT_NE(one, nullptr);
  EXPECT_EQ(vpi_get(vpiType, one), vpiAssignment);
  vpiHandle two = vpi_handle(vpiStmt, Named(vpiTaskFunc, top, "two"));
  ASSERT_NE(two, nullptr);
  EXPECT_EQ(vpi_get(vpiType, two), vpiBegin);
  EXPECT_EQ(ObjectsOf(vpiStmt, two).size(), 2U);
}

TEST_F(ScopesOfARun, AScopeImportsWhatItReferencesThroughAnImport) {
  Run("package p1; int a; int b; int c; int d; endpackage\n"
      "package p2; int e; endpackage\n"
      "module top;\n"
      "  import p1::a;\n"
      "  import p1::d;\n"
      "  import p1::*;\n"
      "  import p2::*;\n"
      "  logic [31:0] w, v;\n"
      "  assign w = a + b + a;\n"
      "  initial begin : blk v = e; end\n"
      "  task t(input int x); v = x; endtask\n"
      "endmodule\n");
  EXPECT_EQ(NamesOf(vpiImport, By("top")),
            (std::vector<std::string>{"a", "b", "e"}));
}

TEST_F(ScopesOfARun, AnObjectOfNoScopeKindReachesNoScope) {
  Run("module top; endmodule\n");
  VpiObject net;
  net.type = vpiNet;
  EXPECT_EQ(vpi_handle(vpiScope, VpiHandleOf(&net)), nullptr);
}

int StmtKindOf(vpiHandle tf) {
  vpiHandle stmt = vpi_handle(vpiStmt, tf);
  return stmt == nullptr ? 0 : vpi_get(vpiType, stmt);
}

TEST_F(ScopesOfARun, EveryTaskReachesTheStatementOfItsBody) {
  Run("int ug;\n"
      "function int uf(); return 1; endfunction\n"
      "package pk; int p; task pt; p = 1; endtask endpackage\n"
      "module top;\n"
      "  int y;\n"
      "  if (1) begin : g task gt; y = 1; y = 2; endtask end\n"
      "endmodule\n");
  EXPECT_EQ(StmtKindOf(Named(vpiTaskFunc, By("top.g"), "gt")), vpiBegin);
  EXPECT_EQ(StmtKindOf(Named(vpiTaskFunc, By("pk"), "pt")), vpiAssignment);
  vpiHandle uf = nullptr;
  vpiHandle it = vpi_iterate(vpiPackage, nullptr);
  while (vpiHandle pkg = it == nullptr ? nullptr : vpi_scan(it)) {
    if (vpiHandle found = Named(vpiTaskFunc, pkg, "uf")) uf = found;
  }
  ASSERT_NE(uf, nullptr);
  EXPECT_EQ(StmtKindOf(uf), vpiReturnStmt);
}

TEST_F(ScopesOfARun, AGenerateBlocksFunctionReachesItsReturn) {
  Run("module top; int r;\n"
      "  if (1) begin : b function int g(); return 2; endfunction end\n"
      "  initial r = b.g();\n"
      "endmodule\n");
  EXPECT_EQ(StmtKindOf(Named(vpiTaskFunc, By("top.b"), "g")), vpiReturnStmt);
}

TEST_F(ScopesOfARun, AClassMethodReachesTheStatementOfItsBody) {
  Run("package pk; class P; int q; task pt; q = 1; endtask endclass "
      "endpackage\n"
      "module top;\n"
      "  class C;\n"
      "    int n;\n"
      "    task ti; n = 1; n = 2; endtask\n"
      "    extern task outside();\n"
      "  endclass\n"
      "  task C::outside(); n = 3; endtask\n"
      "endmodule\n");
  vpiHandle c = Named(vpiClassDefn, By("top"), "C");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(StmtKindOf(Named(vpiTaskFunc, c, "ti")), vpiBegin);
  EXPECT_EQ(StmtKindOf(Named(vpiTaskFunc, c, "outside")), vpiAssignment);
  vpiHandle p = Named(vpiClassDefn, By("pk"), "P");
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(StmtKindOf(Named(vpiTaskFunc, p, "pt")), vpiAssignment);
}

}  // namespace
}  // namespace delta
