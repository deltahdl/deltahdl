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

// §37.5 Module: the VPI object model for a module instance. Most of the diagram
// is structural and is walked by the generic object-model machinery, carrying
// no rule of its own here: the default/global clocking blocks
// (vpiDefaultClocking, vpiGlobalClocking), the default disable-iff
// expr/distribution (vpiDefaultDisableIff), the instance array and module array
// the module belongs to, and the one-to-many vpiInternalScope edges to the
// module's scopes, ports, interfaces, processes, cont assigns, nested modules,
// primitives, mod paths, timing checks, def params, io decls, alias statements,
// and clocking blocks are all reached through vpi_handle / vpi_iterate without
// a clause-specific rule.
//
// This clause carries its own normative content in two numbered Details and two
// module-specific diagram properties, each observed below through the public
// VPI dispatch:
//   D1 - top-level modules are reached by iterating vpiModule with a NULL
//        reference object; a module nested in another scope is excluded.
//   D2 - vpiIndex from a module reaches the index expression that locates it
//        within a module array, or NULL when the module is not an array
//        element.
//   vpiTopModule  - a module reports whether it is a top-level module.
//   vpiDefDecayTime - a module reports its default net decay time.

// The fixture installs a context so the public entry points run their real
// dispatch, and so module objects created through CreateModule are registered
// for the NULL-reference iteration.
class Module : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

// D2: vpiIndex from a module that is an element of a module array reaches the
// index expression that locates it within the array.
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

// D2: for a module that is not part of a module array, the vpiIndex transition
// returns NULL - even when an expr hangs off the object, the transition is
// meaningful only for an array element and must not surface some other child.
TEST_F(Module, IndexTransitionIsNullWhenNotAnArrayElement) {
  VpiObject stray_expr;
  stray_expr.type = vpiConstant;

  VpiObject standalone;
  standalone.type = vpiModule;
  standalone.array_member = false;
  standalone.index_expr = &stray_expr;  // present but must not be reported
  standalone.children.push_back(&stray_expr);

  EXPECT_EQ(vpi_handle(vpiIndex, VpiHandleOf(&standalone)), nullptr);
}

// D1: iterating vpiModule with a NULL reference object reaches the top-level
// modules and only those. A nested module is also a vpiModule object but is
// reached through its parent scope, so it must not appear in this iteration.
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

// vpiTopModule: a module reports whether it is a top-level module through the
// Boolean property, observed via the public vpi_get dispatch.
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

// vpiDefDecayTime: a module reports its default net decay time as an integer
// property through the public vpi_get dispatch.
TEST_F(Module, DefaultDecayTimeReported) {
  VpiObject mod;
  mod.type = vpiModule;
  mod.def_decay_time = 5;
  EXPECT_EQ(vpi_get(vpiDefDecayTime, VpiHandleOf(&mod)), 5);
}

// D1 (edge): when the design contains modules but none is top-level, the
// NULL-reference vpiModule iteration has nothing to walk and reports a null
// handle rather than an iterator over the nested modules. Without the
// top-level filter this iteration would surface the nested module instead.
TEST_F(Module, NullReferenceIterationIsNullWhenNoModuleIsTopLevel) {
  VpiHandle nested = vpi_ctx_.CreateModule("top.sub", "top.sub");
  nested->top_module = false;

  EXPECT_EQ(vpi_iterate(vpiModule, nullptr), nullptr);
}

// D1 (scope guard): the top-level filter applies only to the NULL-reference
// iteration. Iterating vpiModule over a parent scope still reaches the nested
// modules it contains, even though they are not top-level - they are reached
// through the parent, exactly as the object model intends.
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

// -----------------------------------------------------------------------------
// The three tagged edges §37.5 draws beside the module's own details: the
// clocking block it named default, the one it named global, and the expression
// its default disable iff was written with. Each is a relation tag, so the
// generic traversal - which looks for a child whose own type is the type asked
// for - reached none of them from any module.
// -----------------------------------------------------------------------------

// Figure (vpiDefaultClocking / vpiGlobalClocking): a module names at most one
// clocking block of each kind among the blocks it declares, and each edge
// reaches the one so named rather than the first block the module holds.
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

// Figure: a module that named neither reaches neither, rather than whichever
// clocking block it happens to declare first.
TEST_F(Module, AModuleThatNamedNoClockingBlockReachesNone) {
  VpiObject ordinary;
  ordinary.type = vpiClockingBlock;

  VpiObject mod;
  mod.type = kVpiModule;
  mod.children = {&ordinary};

  EXPECT_EQ(vpi_handle(vpiDefaultClocking, VpiHandleOf(&mod)), nullptr);
  EXPECT_EQ(vpi_handle(vpiGlobalClocking, VpiHandleOf(&mod)), nullptr);
}

// Figure (vpiDefaultDisableIff): the edge is drawn to an enclosure with no name
// holding an expr and a distribution, so either is what it reaches: the one the
// scope's default disable iff writes. An expression among the scope's children,
// a parameter's among them, is not.
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

// A design run with a PLI application registered, whose module objects are
// read back for the relations the figure draws.
class ModuleOfARun : public VpiDesignRun {};

// D1 with the figure's port edge: a top-level module reaches its ports, each
// reaching the net inside the module as its lower connection and, with no
// instantiation over the module, no higher one (§37.14 detail 10).
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

// Figure (io decl): a module reaches an io decl per port declaration, whose
// vpiExpr is the net or variable it declares, or a ref obj for a ref port and
// an interface port, the second having no direction (§37.13 details 1 to 3).
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

// Figure (io decl): a port written as an expression is no declaration, so the
// io decls are the declarations it names, one per name however many ports
// select it (§23.2.2.1). An ANSI port written with an explicit name declares
// itself (§23.2.2.2), its vpiExpr the net or variable its expression names and
// null for an expression §37.13's vpiExpr reaches none of.
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

// Figure (module array, instance array): an element of an array reaches the
// array it belongs to, a module array through either tag and an interface
// array through vpiInstanceArray alone; a module of no array reaches none.
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

// vpiDefDecayTime: a module reports the decay time the `default_decay_time
// directive (Annex E.2) set for it, which elaboration records on the module.
TEST_F(ModuleOfARun, AModuleReportsTheDecayTimeItWasCompiledUnder) {
  RtlirDesign* design = ElaborateSrc("module top; endmodule\n", f_);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f_.has_errors);
  // What the directive `default_decay_time 100 ahead of the module records.
  design->top_modules.front()->default_decay_time = 100;
  design->top_modules.front()->default_decay_time_infinite = false;
  LowerAndRun(design, f_);
  EXPECT_EQ(vpi_get(vpiDefDecayTime, By("top")), 100);
}

// Figure (vpiDefaultDisableIff): a module reaches the condition its default
// disable iff (§16.15) writes, rather than any expression it declares.
TEST_F(ModuleOfARun, AModuleReachesTheConditionOfItsDefaultDisableIff) {
  Run("module top #(parameter P = 1); logic rst;\n"
      "  default disable iff !rst;\n"
      "endmodule\n");
  vpiHandle condition = vpi_handle(vpiDefaultDisableIff, By("top"));
  ASSERT_NE(condition, nullptr);
  EXPECT_EQ(OpOf(condition), vpiNotOp);
}

// Figure (vpiDefaultDisableIff): a module under no default disable iff reaches
// none, though it declares a parameter, which is an expression.
TEST_F(ModuleOfARun, AModuleUnderNoDefaultDisableIffReachesNone) {
  Run("module top #(parameter P = 1); endmodule\n");
  EXPECT_EQ(vpi_handle(vpiDefaultDisableIff, By("top")), nullptr);
}

// Figure (alias stmt) with §37.76: a module reaches an alias statement per net
// an alias joins to its last, which is the right-hand side of each.
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

// Figure (def param) with §37.28: a module reaches a def param per parameter
// its defparam changes, reaching that parameter through vpiLhs and the value
// written through vpiRhs.
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
