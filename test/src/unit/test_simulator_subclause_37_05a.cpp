#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "elaborator/rtlir.h"
#include "fixture_simulator.h"
#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class Module : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

TEST_F(Module, IndexTransitionReachesArrayIndex) {
  VpiObject index_expr;
  index_expr.type = vpiConstant;

  VpiObject member;
  member.type = vpiModule;
  member.array_member = true;
  member.index_expr = &index_expr;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiIndex, VpiHandleOf(&member))),
            &index_expr);
}

TEST_F(Module, IndexTransitionIsNullWhenNotAnArrayElement) {
  VpiObject stray_expr;
  stray_expr.type = vpiConstant;

  VpiObject standalone;
  standalone.type = vpiModule;
  standalone.array_member = false;
  standalone.index_expr = &stray_expr;
  standalone.children.push_back(&stray_expr);

  EXPECT_EQ(vpi_handle(vpiIndex, VpiHandleOf(&standalone)), nullptr);
}

TEST_F(Module, TopModulesReachedByNullReferenceIteration) {
  VpiHandle top = vpi_ctx_.CreateModule("top", "top");
  top->top_module = true;

  VpiHandle nested = vpi_ctx_.CreateModule("top.sub", "top.sub");
  nested->top_module = false;

  vpiHandle it = vpi_iterate(vpiModule, nullptr);
  ASSERT_NE(it, nullptr);
  int count = 0;
  bool saw_top = false;
  bool saw_nested = false;
  while (vpiHandle h = vpi_scan(it)) {
    ++count;
    if (VpiObjectOf(h) == top) saw_top = true;
    if (VpiObjectOf(h) == nested) saw_nested = true;
  }
  EXPECT_EQ(count, 1);
  EXPECT_TRUE(saw_top);
  EXPECT_FALSE(saw_nested);
}

TEST_F(Module, TopModulePropertyReportsTopLevelStatus) {
  VpiObject top;
  top.type = vpiModule;
  top.top_module = true;
  EXPECT_EQ(vpi_get(vpiTopModule, VpiHandleOf(&top)), 1);

  VpiObject nested;
  nested.type = vpiModule;
  nested.top_module = false;
  EXPECT_EQ(vpi_get(vpiTopModule, VpiHandleOf(&nested)), 0);
}

TEST_F(Module, DefaultDecayTimeReported) {
  VpiObject mod;
  mod.type = vpiModule;
  mod.def_decay_time = 5;
  EXPECT_EQ(vpi_get(vpiDefDecayTime, VpiHandleOf(&mod)), 5);
}

TEST_F(Module, NullReferenceIterationIsNullWhenNoModuleIsTopLevel) {
  VpiHandle nested = vpi_ctx_.CreateModule("top.sub", "top.sub");
  nested->top_module = false;

  EXPECT_EQ(vpi_iterate(vpiModule, nullptr), nullptr);
}

TEST_F(Module, ModuleIterationOverParentScopeIsNotFilteredByTopLevel) {
  VpiHandle parent = vpi_ctx_.CreateModule("top", "top");
  parent->top_module = true;

  VpiHandle nested = vpi_ctx_.CreateModule("top.sub", "top.sub");
  nested->top_module = false;
  parent->children.push_back(nested);

  vpiHandle it = vpi_iterate(vpiModule, VpiHandleOf(parent));
  ASSERT_NE(it, nullptr);
  int count = 0;
  bool saw_nested = false;
  while (vpiHandle h = vpi_scan(it)) {
    ++count;
    if (VpiObjectOf(h) == nested) saw_nested = true;
  }
  EXPECT_EQ(count, 1);
  EXPECT_TRUE(saw_nested);
}

TEST_F(Module, AModuleReachesTheClockingBlocksItNamed) {
  VpiObject ordinary;
  ordinary.type = vpiClockingBlock;
  VpiObject global_block;
  global_block.type = vpiClockingBlock;
  global_block.global_clocking = true;
  VpiObject default_block;
  default_block.type = vpiClockingBlock;
  default_block.default_clocking = true;

  VpiObject mod;
  mod.type = kVpiModule;
  mod.children = {&ordinary, &global_block, &default_block};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiDefaultClocking, VpiHandleOf(&mod))),
            &default_block);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiGlobalClocking, VpiHandleOf(&mod))),
            &global_block);
}

TEST_F(Module, AModuleThatNamedNoClockingBlockReachesNone) {
  VpiObject ordinary;
  ordinary.type = vpiClockingBlock;

  VpiObject mod;
  mod.type = kVpiModule;
  mod.children = {&ordinary};

  EXPECT_EQ(vpi_handle(vpiDefaultClocking, VpiHandleOf(&mod)), nullptr);
  EXPECT_EQ(vpi_handle(vpiGlobalClocking, VpiHandleOf(&mod)), nullptr);
}

TEST_F(Module, AModuleReachesItsDefaultDisableIff) {
  VpiObject param;
  param.type = vpiParameter;
  VpiObject condition;
  condition.type = vpiOperation;

  VpiObject mod;
  mod.type = kVpiModule;
  mod.children = {&param};
  mod.disable_condition = &condition;
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiDefaultDisableIff, VpiHandleOf(&mod))),
            &condition);

  VpiObject plain;
  plain.type = kVpiModule;
  plain.children = {&param};
  EXPECT_EQ(vpi_handle(vpiDefaultDisableIff, VpiHandleOf(&plain)), nullptr);
}

class ModuleOfARun : public VpiDesignRun {};

TEST_F(ModuleOfARun, ATopModuleReachesItsPorts) {
  Run("module top(input logic a, output logic b); assign b = a; endmodule\n");
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  EXPECT_EQ(NamesOf(vpiPort, top), (std::vector<std::string>{"a", "b"}));
  vpiHandle a = Named(vpiPort, top, "a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(vpi_handle(vpiHighConn, a), nullptr);
  vpiHandle low = vpi_handle(vpiLowConn, a);
  ASSERT_NE(low, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, low), "a");
}

TEST_F(ModuleOfARun, AModuleReachesAnIoDeclPerPortDeclaration) {
  Run("interface ifc; endinterface\n"
      "module sub(input logic [3:0] d, ref int r, ifc bus); endmodule\n"
      "module top; logic [3:0] w; int x;\n"
      "  ifc i (); sub u (.d(w), .r(x), .bus(i));\n"
      "endmodule\n");
  vpiHandle u = By("top.u");
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(NamesOf(vpiIODecl, u), (std::vector<std::string>{"bus", "d", "r"}));
  vpiHandle d = Named(vpiIODecl, u, "d");
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(vpi_get(vpiDirection, d), vpiInput);
  vpiHandle d_expr = vpi_handle(vpiExpr, d);
  ASSERT_NE(d_expr, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, d_expr), "d");
  vpiHandle r = Named(vpiIODecl, u, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(vpi_get(vpiDirection, r), vpiRef);
  vpiHandle r_expr = vpi_handle(vpiExpr, r);
  ASSERT_NE(r_expr, nullptr);
  EXPECT_EQ(vpi_get(vpiType, r_expr), vpiRefObj);
  vpiHandle bus = Named(vpiIODecl, u, "bus");
  ASSERT_NE(bus, nullptr);
  EXPECT_EQ(vpi_get(vpiDirection, bus), vpiNoDirection);
  vpiHandle bus_expr = vpi_handle(vpiExpr, bus);
  ASSERT_NE(bus_expr, nullptr);
  EXPECT_EQ(vpi_get(vpiType, bus_expr), vpiRefObj);
}

TEST_F(ModuleOfARun, APortWrittenAsAnExpressionHasAnIoDeclPerDeclaration) {
  Run("module sel(a[1], a[0]); input [1:0] a; endmodule\n"
      "module cat({b, c}, .p(e)); input b; output c; input e; endmodule\n"
      "module ansi(output .P1(r[3:0]), input .P2(s));\n"
      "  logic [7:0] r; logic s;\n"
      "endmodule\n"
      "module top; logic [1:0] v; logic x, y, z, t; logic [3:0] q;\n"
      "  sel u1 (v[1], v[0]); cat u2 ({x, y}, z); ansi u3 (q, t);\n"
      "endmodule\n");
  vpiHandle u1 = By("top.u1");
  ASSERT_NE(u1, nullptr);
  EXPECT_EQ(NamesOf(vpiIODecl, u1), (std::vector<std::string>{"a"}));
  vpiHandle u2 = By("top.u2");
  ASSERT_NE(u2, nullptr);
  EXPECT_EQ(NamesOf(vpiIODecl, u2), (std::vector<std::string>{"b", "c", "e"}));
  vpiHandle c = Named(vpiIODecl, u2, "c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(vpi_get(vpiDirection, c), vpiOutput);
  vpiHandle c_expr = vpi_handle(vpiExpr, c);
  ASSERT_NE(c_expr, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, c_expr), "c");
  vpiHandle u3 = By("top.u3");
  ASSERT_NE(u3, nullptr);
  EXPECT_EQ(NamesOf(vpiIODecl, u3), (std::vector<std::string>{"P1", "P2"}));
  vpiHandle p1 = Named(vpiIODecl, u3, "P1");
  ASSERT_NE(p1, nullptr);
  EXPECT_EQ(vpi_get(vpiDirection, p1), vpiOutput);
  EXPECT_EQ(vpi_handle(vpiExpr, p1), nullptr);
  vpiHandle p2_expr = vpi_handle(vpiExpr, Named(vpiIODecl, u3, "P2"));
  ASSERT_NE(p2_expr, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, p2_expr), "s");
}

TEST_F(ModuleOfARun, AnArrayElementReachesItsArray) {
  Run("module sub; endmodule\n"
      "interface ifc; endinterface\n"
      "module top; sub arr[1:0] (); sub one (); ifc ifs[0:1] (); endmodule\n");
  vpiHandle element = By("top.arr[1]");
  ASSERT_NE(element, nullptr);
  VpiObject* arr = VpiObjectOf(By("top.arr"));
  ASSERT_NE(arr, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiModuleArray, element)), arr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiInstanceArray, element)), arr);
  vpiHandle one = By("top.one");
  ASSERT_NE(one, nullptr);
  EXPECT_EQ(vpi_handle(vpiModuleArray, one), nullptr);
  EXPECT_EQ(vpi_handle(vpiInstanceArray, one), nullptr);
  vpiHandle iface = By("top.ifs[0]");
  ASSERT_NE(iface, nullptr);
  EXPECT_EQ(vpi_handle(vpiModuleArray, iface), nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiInstanceArray, iface)),
            VpiObjectOf(By("top.ifs")));
}

TEST_F(ModuleOfARun, AModuleReportsTheDecayTimeItWasCompiledUnder) {
  RtlirDesign* design = ElaborateSrc("module top; endmodule\n", f_);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f_.has_errors);
  design->top_modules.front()->default_decay_time = 100;
  design->top_modules.front()->default_decay_time_infinite = false;
  LowerAndRun(design, f_);
  EXPECT_EQ(vpi_get(vpiDefDecayTime, By("top")), 100);
}

TEST_F(ModuleOfARun, AModuleWhoseChargeNeverDecaysHasAnUndefinedDecayTime) {
  Run("module top; endmodule\n");
  EXPECT_EQ(vpi_get(vpiDefDecayTime, By("top")), vpiUndefined);
}

TEST_F(ModuleOfARun, AModuleWhoseChargeDecaysAtOnceReportsADecayTimeOfZero) {
  RtlirDesign* design = ElaborateSrc("module top; endmodule\n", f_);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f_.has_errors);
  design->top_modules.front()->default_decay_time = 0;
  design->top_modules.front()->default_decay_time_infinite = false;
  LowerAndRun(design, f_);
  EXPECT_EQ(vpi_get(vpiDefDecayTime, By("top")), 0);
}

TEST_F(ModuleOfARun, AModuleReachesTheConditionOfItsDefaultDisableIff) {
  Run("module top #(parameter P = 1); logic rst;\n"
      "  default disable iff !rst;\n"
      "endmodule\n");
  vpiHandle condition = vpi_handle(vpiDefaultDisableIff, By("top"));
  ASSERT_NE(condition, nullptr);
  EXPECT_EQ(OpOf(condition), vpiNotOp);
}

TEST_F(ModuleOfARun, AModuleUnderNoDefaultDisableIffReachesNone) {
  Run("module top #(parameter P = 1); endmodule\n");
  EXPECT_EQ(vpi_handle(vpiDefaultDisableIff, By("top")), nullptr);
}

TEST_F(ModuleOfARun, AModuleReachesAnAliasStatementPerNetItJoins) {
  Run("module top; wire a, b, c; alias a = b = c; endmodule\n");
  std::vector<vpiHandle> stmts = ObjectsOf(vpiAliasStmt, By("top"));
  ASSERT_EQ(stmts.size(), 2U);
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiLhs, stmts[0])), "a");
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiLhs, stmts[1])), "b");
  for (vpiHandle stmt : stmts) {
    EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiRhs, stmt)), "c");
  }
}

TEST_F(ModuleOfARun, AModuleReachesADefParamPerParameterItChanges) {
  Run("module sub #(parameter W = 1); endmodule\n"
      "module top; sub u (); defparam u.W = 8; endmodule\n");
  std::vector<vpiHandle> defparams = ObjectsOf(vpiDefParam, By("top"));
  ASSERT_EQ(defparams.size(), 1U);
  vpiHandle lhs = vpi_handle(vpiLhs, defparams[0]);
  ASSERT_NE(lhs, nullptr);
  EXPECT_EQ(VpiObjectOf(lhs),
            VpiObjectOf(Named(vpiParameter, By("top.u"), "W")));
  vpiHandle rhs = vpi_handle(vpiRhs, defparams[0]);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(vpi_get(vpiType, rhs), vpiConstant);
}

}  // namespace
}  // namespace delta
