#include <gtest/gtest.h>

#include <cstddef>
#include <deque>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "elaborator/rtlir.h"
#include "fixture_simulator.h"
#include "fixture_vpi_run.h"
#include "parser/ast_expr.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// §37.42: the calls a design writes outside every procedure - in a port
// connection, a primitive terminal, a clocking block, a constraint, a
// package's property, a modport port and an extends clause - each the tf call
// a procedure's call is, named, standing in its scope (§37.12) and reaching
// what it calls.
class CallsOutsideProcedures : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    s_vpi_systf_data data = {};
    data.type = vpiSysFunc;
    data.sysfunctype = vpiIntFunc;
    data.tfname = VpiText("$sf");
    data.calltf = &VpiDesignRunCalltf;
    sf_ = vpi_register_systf(&data);
    ASSERT_NE(sf_, nullptr);
  }

  // Checks that `call` is a func call of the function `name`, standing in
  // `scope`.
  static void ExpectFunctionCall(vpiHandle call, const char* name,
                                 vpiHandle scope) {
    ASSERT_NE(call, nullptr);
    EXPECT_EQ(vpi_get(vpiType, call), vpiFuncCall);
    EXPECT_STREQ(vpi_get_str(vpiName, call), name);
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiScope, call)), VpiObjectOf(scope));
    vpiHandle function = vpi_handle(vpiFunction, call);
    ASSERT_NE(function, nullptr);
    EXPECT_STREQ(vpi_get_str(vpiName, function), name);
  }

  // Checks that `call` is a call of $sf, standing in `scope` and reaching the
  // systf its registration returned (detail 5).
  void ExpectSystemCall(vpiHandle call, vpiHandle scope) const {
    ASSERT_NE(call, nullptr);
    EXPECT_EQ(vpi_get(vpiType, call), vpiSysFuncCall);
    EXPECT_STREQ(vpi_get_str(vpiName, call), "$sf");
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiScope, call)), VpiObjectOf(scope));
    EXPECT_EQ(vpi_get(vpiUserDefn, call), 1);
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiUserSystf, call)), VpiObjectOf(sf_));
  }

  // What the first port of the instance `name` is connected to.
  static vpiHandle HighConnOf(const std::string& name) {
    const std::vector<vpiHandle> kPorts = ObjectsOf(vpiPort, By(name));
    return kPorts.empty() ? nullptr : vpi_handle(vpiHighConn, kPorts[0]);
  }

  // The operand number `n` of the operation `op`, null for none.
  static vpiHandle OperandOf(vpiHandle op, std::size_t n) {
    const std::vector<vpiHandle> kOperands = OperandsOf(op);
    return n < kOperands.size() ? kOperands[n] : nullptr;
  }

  vpiHandle sf_ = nullptr;
};

// A call a port connection makes stands in the instance writing the
// connection (#7279).
TEST_F(CallsOutsideProcedures, APortConnectionsCallIsShaped) {
  Run("module sub(input logic [31:0] a); endmodule\n"
      "module top; int x;\n"
      "  function automatic int f(int v); return v; endfunction\n"
      "  sub u (.a(f(x)));\n"
      "  sub w (.a($sf(x)));\n"
      "endmodule\n");
  ExpectFunctionCall(HighConnOf("top.u"), "f", By("top"));
  ExpectSystemCall(HighConnOf("top.w"), By("top"));
}

// A call a primitive's terminal makes stands in the instance (#7282).
TEST_F(CallsOutsideProcedures, APrimitiveTerminalsCallIsShaped) {
  Run("module top; wire y, z; logic b;\n"
      "  function automatic logic f(logic v); return v; endfunction\n"
      "  and g (y, f(b), b);\n"
      "  or h (z, $sf(b), b);\n"
      "endmodule\n");
  const auto kInputOf = [](const char* gate) {
    const std::vector<vpiHandle> kTerms =
        ObjectsOf(vpiPrimTerm, Named(vpiPrimitive, By("top"), gate));
    return kTerms.size() > 1 ? vpi_handle(vpiExpr, kTerms[1]) : nullptr;
  };
  ExpectFunctionCall(kInputOf("g"), "f", By("top"));
  ExpectSystemCall(kInputOf("h"), By("top"));
}

// A call a clocking block's event is written with stands in the block, a
// scope of its own (§37.12) (#7283).
TEST_F(CallsOutsideProcedures, AClockingBlocksCallIsShaped) {
  Run("module top; logic clk;\n"
      "  function automatic logic f(logic v); return v; endfunction\n"
      "  clocking cb @(posedge f(clk)); endclocking\n"
      "  clocking cs @(posedge $sf(clk)); endclocking\n"
      "endmodule\n");
  const auto kEdgeOf = [](vpiHandle block) {
    vpiHandle event = vpi_handle(vpiClockingEvent, block);
    return OperandOf(
        event == nullptr ? nullptr : vpi_handle(vpiCondition, event), 0);
  };
  vpiHandle cb = Named(vpiClockingBlock, By("top"), "cb");
  vpiHandle cs = Named(vpiClockingBlock, By("top"), "cs");
  ASSERT_NE(cb, nullptr);
  ASSERT_NE(cs, nullptr);
  ExpectFunctionCall(kEdgeOf(cb), "f", cb);
  ExpectSystemCall(kEdgeOf(cs), cs);
}

// A call a constraint makes stands in the class declaring it (#7284).
TEST_F(CallsOutsideProcedures, AConstraintsCallIsShaped) {
  Run("module top;\n"
      "  function automatic int f(int v); return v; endfunction\n"
      "  class C; rand int x; constraint c { x < f(5); x > $sf(1); }\n"
      "  endclass\n"
      "endmodule\n");
  vpiHandle defn = Named(vpiClassDefn, By("top"), "C");
  ASSERT_NE(defn, nullptr);
  const std::vector<vpiHandle> kItems =
      ObjectsOf(vpiConstraintItem, Named(vpiConstraint, defn, "c"));
  ASSERT_EQ(kItems.size(), 2U);
  ExpectFunctionCall(OperandOf(kItems[0], 1), "f", defn);
  ExpectSystemCall(OperandOf(kItems[1], 1), defn);
}

// A call a package's property makes stands in the package, its callee found
// among the package's own functions, as a package sees no other but by
// import (§26.2) (#7285).
TEST_F(CallsOutsideProcedures, APackagePropertysCallIsShaped) {
  Run("package pk;\n"
      "  function automatic int f(int v); return v; endfunction\n"
      "  property q(x); f(x) == $sf(x); endproperty\n"
      "endpackage\n"
      "module top; endmodule\n");
  vpiHandle pk = By("pk");
  ASSERT_NE(pk, nullptr);
  vpiHandle spec = vpi_handle(vpiPropertySpec, Named(vpiPropertyDecl, pk, "q"));
  ASSERT_NE(spec, nullptr);
  vpiHandle equality = vpi_handle(vpiPropertyExpr, spec);
  ExpectFunctionCall(OperandOf(equality, 0), "f", pk);
  ExpectSystemCall(OperandOf(equality, 1), pk);
}

// A call a constraint of a package's class makes finds its callee among the
// package's functions too (§26.2).
TEST_F(CallsOutsideProcedures, APackageClasssConstraintFindsItsCallee) {
  Run("package pk;\n"
      "  function automatic int f(int v); return v; endfunction\n"
      "  class C; rand int x; constraint c { x < f(5); } endclass\n"
      "endpackage\n"
      "module top; endmodule\n");
  vpiHandle defn = Named(vpiClassDefn, By("pk"), "C");
  ASSERT_NE(defn, nullptr);
  const std::vector<vpiHandle> kItems =
      ObjectsOf(vpiConstraintItem, Named(vpiConstraint, defn, "c"));
  ASSERT_EQ(kItems.size(), 1U);
  ExpectFunctionCall(OperandOf(kItems[0], 1), "f", defn);
}

// A call a modport port's expression makes stands in the interface instance
// (#7286).
TEST_F(CallsOutsideProcedures, AModportPortsCallIsShaped) {
  Run("interface ifc; int a;\n"
      "  function automatic int f(int v); return v; endfunction\n"
      "  modport mp (input .i(f(a)), input .j($sf(a)));\n"
      "endinterface\n"
      "module top; ifc u (); endmodule\n");
  vpiHandle u = By("top.u");
  ASSERT_NE(u, nullptr);
  const std::vector<vpiHandle> kDecls =
      ObjectsOf(vpiIODecl, Named(vpiModport, u, "mp"));
  ASSERT_EQ(kDecls.size(), 2U);
  ExpectFunctionCall(vpi_handle(vpiExpr, kDecls[0]), "f", u);
  ExpectSystemCall(vpi_handle(vpiExpr, kDecls[1]), u);
}

// A call an extends clause passes stands in the derived class (#7287).
TEST_F(CallsOutsideProcedures, AnExtendsClausesCallIsShaped) {
  Run("module top;\n"
      "  function automatic int f(int v); return v; endfunction\n"
      "  class B; function new(int n); endfunction endclass\n"
      "  class D extends B(f(1)); endclass\n"
      "  class E extends B($sf(1)); endclass\n"
      "endmodule\n");
  const auto kPassed = [](vpiHandle defn) {
    const std::vector<vpiHandle> kArgs =
        ObjectsOf(vpiArgument, vpi_handle(vpiExtends, defn));
    return kArgs.empty() ? nullptr : kArgs[0];
  };
  vpiHandle d = Named(vpiClassDefn, By("top"), "D");
  vpiHandle e = Named(vpiClassDefn, By("top"), "E");
  ASSERT_NE(d, nullptr);
  ASSERT_NE(e, nullptr);
  ExpectFunctionCall(kPassed(d), "f", d);
  ExpectSystemCall(kPassed(e), e);
}

// A held call whose callee no shape resolves - here none is written - keeps
// the arguments it is written with, as an unshaped call does.
TEST(DeferredCallModel, ACallNoShapeResolvesKeepsItsArguments) {
  SimFixture f;
  RtlirDesign* design = ElaborateSrc("module top; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  std::deque<VpiObject> made;
  std::deque<std::string> kept;
  const VpiAttachBuild kBuild{[&made] { return &made.emplace_back(); },
                              [&kept](std::string name) {
                                kept.push_back(std::move(name));
                                return std::string_view(kept.back());
                              },
                              f.arena};
  VpiCallSiteObjects sites;
  VpiStmtObjects stmts;
  const VpiCallObjects kObjects;
  const VpiCallBuild kCalls{
      f.ctx,
      [](std::string_view) { return VpiRegisteredSystf{}; },
      sites,
      stmts,
      kObjects.classes,
      kObjects.subroutines,
      kObjects.unit_typespecs};
  Expr argument;
  argument.kind = ExprKind::kIntegerLiteral;
  argument.text = "7";
  argument.int_val = 7;
  Expr call;
  call.kind = ExprKind::kCall;
  call.args = {&argument};
  VpiObject scope;
  scope.type = vpiModule;
  VpiObject held;
  held.type = vpiFuncCall;
  std::vector<VpiDeferredCall> deferred = {
      {&call, &held, VpiCallStand{&scope}, "top", {}}};
  VpiShapeDeferredCalls(*design, {}, deferred, kCalls, kBuild);
  ASSERT_EQ(held.arguments.size(), 1U);
  EXPECT_EQ(held.arguments[0]->type, vpiConstant);
  EXPECT_EQ(held.parent, nullptr);
}

}  // namespace
}  // namespace delta
