#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// §37.12 against a design run: the scope class's relations read back from the
// objects a run builds.
class ScopesOfARun : public VpiDesignRun {};

// The figure: each internal scope reaches through vpiScope the scope that
// holds it -- a task, a function and a module instance their module -- and a
// top, held by none, reaches none.
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

// Detail 7 with §37.29 example 1: a scope's vpiVirtualInterfaceVar iteration
// returns a virtual interface var standing alone and each element of an
// array of virtual interfaces.
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

// Detail 5: a task's or function's vpiStmt is its one statement, an unnamed
// begin holding them where it holds more than one, the declaration it opens
// with none of them, and null where it holds none.
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

// Detail 4: a scope's vpiImport iteration returns the objects its module's
// imports bring in that it references, by name or through a wildcard, each
// once however often it is referenced, and none it imports but never reads.
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

// The figure draws vpiScope from statements, calls and the kinds the scope
// class groups; a net standing in no scope reaches none.
TEST_F(ScopesOfARun, AnObjectOfNoScopeKindReachesNoScope) {
  Run("module top; endmodule\n");
  VpiObject net;
  net.type = vpiNet;
  EXPECT_EQ(vpi_handle(vpiScope, VpiHandleOf(&net)), nullptr);
}

}  // namespace
}  // namespace delta
