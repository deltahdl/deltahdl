#include <gtest/gtest.h>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// §37.48 Clocking block: a clocking block (vpiClockingBlock) groups the default
// input/output skews, the clocking event, and the clocking io decls
// (vpiClockingIODecl) it contains. These tests observe the production code that
// applies the clause's three numbered "Details" that refine traversal -
// vpiPrefix (detail 2), vpiActual (detail 3), and an io decl's vpiExpr (detail
// 4) - and the figure's vpiClockingEvent edge, through the same-pipeline public
// vpi_handle dispatch. Like vpiPrefix/vpiActual/vpiExpr, the vpiClockingEvent
// relation reaches an object whose type tag differs from the relation tag, so
// the generic child walk cannot serve it and a dedicated helper carries it.
// Detail 1 only records which construct the skew/edge relations target, and the
// figure's remaining structural relations and properties are served by the
// generic machinery; neither refines behavior here.

// The fixture installs a context so the public vpi_handle entry point runs its
// real dispatch over the test objects.
class ClockingBlock : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// D2: vpiPrefix of a clocking block reaches the virtual interface var the
// clocking block expression is immediately prefixed by. Observed through the
// helper and the public vpi_handle(vpiPrefix, ...) dispatch. The relation is
// non-NULL exactly because the clocking block carries that prefix.
TEST_F(ClockingBlock, PrefixReachesVirtualInterfacePrefix) {
  VpiObject vif;  // the virtual interface that prefixes the clocking block
  vif.type = vpiVirtualInterfaceVar;

  VpiObject block;
  block.type = vpiClockingBlock;
  block.children = {&vif};

  EXPECT_EQ(VpiClockingBlockPrefix(&block), &vif);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiPrefix, VpiHandleOf(&block))), &vif);
}

// D2: a clocking block that is not a virtual-interface-prefixed expression has
// no virtual interface var prefix, so vpiPrefix reports NULL rather than
// reaching some unrelated child.
TEST_F(ClockingBlock, PrefixIsNullWhenNotVirtualInterfacePrefixed) {
  VpiObject event_ctrl;  // an ordinary (non-vif) child of the clocking block
  event_ctrl.type = vpiEventControl;

  VpiObject block;
  block.type = vpiClockingBlock;
  block.children = {&event_ctrl};

  EXPECT_EQ(VpiClockingBlockPrefix(&block), nullptr);
  EXPECT_EQ(vpi_handle(vpiPrefix, VpiHandleOf(&block)), nullptr);
}

// D3: vpiActual of a clocking block reaches the concrete clocking block
// selected through its virtual interface prefix when that prefix holds a value
// at the current simulation time (its own vpiActual is bound).
TEST_F(ClockingBlock, ActualReachesResolvedClockingBlockWhenPrefixHasValue) {
  VpiObject iface;  // the interface the virtual interface currently holds
  iface.type = vpiInterface;

  VpiObject vif;
  vif.type = vpiVirtualInterfaceVar;
  vif.actual = &iface;  // prefix has a value at the current simulation time

  VpiObject
      resolved;  // the concrete clocking block selected through the prefix
  resolved.type = vpiClockingBlock;

  VpiObject block;
  block.type = vpiClockingBlock;
  block.children = {&vif};
  block.actual = &resolved;

  EXPECT_EQ(VpiClockingBlockActual(&block), &resolved);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiActual, VpiHandleOf(&block))), &resolved);
}

// D3: when the prefix is a virtual interface that has no value at the current
// simulation time - its own vpiActual being NULL - the clocking block's
// vpiActual is NULL as well, even though a resolved actual is otherwise
// present.
TEST_F(ClockingBlock, ActualIsNullWhenVirtualInterfacePrefixHasNoValue) {
  VpiObject vif;
  vif.type = vpiVirtualInterfaceVar;  // uninitialized: no value bound yet

  VpiObject resolved;
  resolved.type = vpiClockingBlock;

  VpiObject block;
  block.type = vpiClockingBlock;
  block.children = {&vif};
  block.actual = &resolved;  // present, but suppressed by the empty prefix

  EXPECT_EQ(VpiClockingBlockActual(&block), nullptr);
  EXPECT_EQ(vpi_handle(vpiActual, VpiHandleOf(&block)), nullptr);
}

// D3 edge: the no-value suppression is gated on a virtual interface prefix. A
// clocking block that is not prefixed by a virtual interface reports its actual
// directly, so the detail-3 rule does not steal an otherwise valid traversal.
TEST_F(ClockingBlock, ActualReachesActualWhenNotVirtualInterfacePrefixed) {
  VpiObject resolved;
  resolved.type = vpiClockingBlock;

  VpiObject block;
  block.type = vpiClockingBlock;  // no virtual interface var child
  block.actual = &resolved;

  EXPECT_EQ(VpiClockingBlockActual(&block), &resolved);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiActual, VpiHandleOf(&block))), &resolved);
}

// Figure (clocking io decl -> nets / variables / ref obj): the io-decl expr
// predicate recognizes a ref obj, a net, and a variable of any kind the
// `variables` class groups (§37.4.1) -- a logic var and an int var alike -- and
// rejects an unrelated kind such as a delay control.
TEST_F(ClockingBlock, IODeclExprGroupMembership) {
  EXPECT_TRUE(VpiIsClockingIODeclExprType(vpiRefObj));
  EXPECT_TRUE(VpiIsClockingIODeclExprType(kVpiNet));
  EXPECT_TRUE(VpiIsClockingIODeclExprType(kVpiReg));
  EXPECT_TRUE(VpiIsClockingIODeclExprType(vpiIntVar));
  EXPECT_TRUE(VpiIsClockingIODeclExprType(vpiStringVar));
  EXPECT_FALSE(VpiIsClockingIODeclExprType(vpiDelayControl));
}

// D4: vpiExpr of a clocking io decl reaches the ref obj the io decl names. This
// is the clause's own example - the io decl "enable" reaches "top.mem1.enable".
// Observed through the helper and the public vpi_handle(vpiExpr, ...) dispatch.
TEST_F(ClockingBlock, IODeclExprReachesNamedRefObj) {
  VpiObject ref;  // the ref obj "top.mem1.enable" the io decl names
  ref.type = vpiRefObj;

  VpiObject io_decl;
  io_decl.type = vpiClockingIODecl;
  io_decl.children = {&ref};

  EXPECT_EQ(VpiClockingIODeclExpr(&io_decl), &ref);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, VpiHandleOf(&io_decl))), &ref);
}

// D4: a clocking io decl whose only children are its skews names no expression,
// so vpiExpr reports NULL rather than handing back a skew's delay control.
TEST_F(ClockingBlock, IODeclExprIsNullWhenNothingNamed) {
  VpiObject skew;  // an input/output skew delay control, not the named expr
  skew.type = vpiDelayControl;

  VpiObject io_decl;
  io_decl.type = vpiClockingIODecl;
  io_decl.children = {&skew};

  EXPECT_EQ(VpiClockingIODeclExpr(&io_decl), nullptr);
  EXPECT_EQ(vpi_handle(vpiExpr, VpiHandleOf(&io_decl)), nullptr);
}

// D4 input form (figure clocking io decl -> nets): the named target need not be
// a ref obj. When the io decl directly names a net - as an io decl bound to a
// signal declared as a net does - vpiExpr reaches that net, past a leading skew
// delay control that is not the named expression.
TEST_F(ClockingBlock, IODeclExprReachesNamedNet) {
  VpiObject skew;  // a leading input skew, not the named expression
  skew.type = vpiDelayControl;

  VpiObject net;  // the net the io decl names
  net.type = kVpiNet;

  VpiObject io_decl;
  io_decl.type = vpiClockingIODecl;
  io_decl.children = {&skew, &net};

  EXPECT_EQ(VpiClockingIODeclExpr(&io_decl), &net);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, VpiHandleOf(&io_decl))), &net);
}

// D4 input form (figure clocking io decl -> variables): the named target may be
// a variable rather than a ref obj or net - the case of an io decl bound to a
// signal declared as a variable (e.g. "output q" where q is a reg). vpiExpr
// reaches that variable through the same resolver, completing the figure's
// three-way {nets, variables, ref obj} reach.
TEST_F(ClockingBlock, IODeclExprReachesNamedVariable) {
  VpiObject var;  // the variable the io decl names
  var.type = kVpiReg;

  VpiObject io_decl;
  io_decl.type = vpiClockingIODecl;
  io_decl.children = {&var};

  EXPECT_EQ(VpiClockingIODeclExpr(&io_decl), &var);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, VpiHandleOf(&io_decl))), &var);
}

// D4 input form (figure clocking io decl -> variables grouping): the named
// target may be any variable the `variables` class groups (§37.4.1), not only
// the logic var whose code the reg shares. vpiExpr reaches it through the same
// resolver, so the grouping arm is observed end to end and not just at the type
// predicate.
TEST_F(ClockingBlock, IODeclExprReachesVariablesGrouping) {
  VpiObject var;  // a variable of a kind the variables class groups
  var.type = vpiIntVar;

  VpiObject io_decl;
  io_decl.type = vpiClockingIODecl;
  io_decl.children = {&var};

  EXPECT_EQ(VpiClockingIODeclExpr(&io_decl), &var);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, VpiHandleOf(&io_decl))), &var);
}

// Figure (clocking block -> event control via vpiClockingEvent): the clocking
// event driving the block is reached through vpiClockingEvent, modeled as an
// event-control child. Observed through the helper and the public
// vpi_handle(vpiClockingEvent, ...) dispatch - the generic child walk cannot
// serve it because the relation and object tags differ.
TEST_F(ClockingBlock, ClockingEventReachesEventControl) {
  VpiObject event_ctrl;  // the "@(posedge clk)" driving the block
  event_ctrl.type = vpiEventControl;

  VpiObject block;
  block.type = vpiClockingBlock;
  block.children = {&event_ctrl};

  EXPECT_EQ(VpiClockingBlockClockingEvent(&block), &event_ctrl);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiClockingEvent, VpiHandleOf(&block))),
            &event_ctrl);
}

// Figure (clocking block -> event control): a clocking block that carries no
// event control reaches nothing through vpiClockingEvent rather than handing
// back some unrelated child such as a virtual interface prefix.
TEST_F(ClockingBlock, ClockingEventIsNullWhenNoEventControl) {
  VpiObject vif;  // an unrelated (non-event-control) child
  vif.type = vpiVirtualInterfaceVar;

  VpiObject block;
  block.type = vpiClockingBlock;
  block.children = {&vif};

  EXPECT_EQ(VpiClockingBlockClockingEvent(&block), nullptr);
  EXPECT_EQ(vpi_handle(vpiClockingEvent, VpiHandleOf(&block)), nullptr);
}

// Edge: each clocking-block helper speaks only for its own object kind, so an
// unrelated handle (or a null handle) reaches nothing through it. This guards
// the dispatch from misapplying the detail rules to the wrong object.
TEST_F(ClockingBlock, HelpersGuardOnObjectKind) {
  VpiObject other;
  other.type = vpiModule;

  EXPECT_EQ(VpiClockingBlockPrefix(&other), nullptr);
  EXPECT_EQ(VpiClockingBlockPrefix(nullptr), nullptr);
  EXPECT_EQ(VpiClockingBlockActual(&other), nullptr);
  EXPECT_EQ(VpiClockingBlockActual(nullptr), nullptr);
  EXPECT_EQ(VpiClockingIODeclExpr(&other), nullptr);
  EXPECT_EQ(VpiClockingIODeclExpr(nullptr), nullptr);
  EXPECT_EQ(VpiClockingBlockClockingEvent(&other), nullptr);
  EXPECT_EQ(VpiClockingBlockClockingEvent(nullptr), nullptr);
}

// The clocking blocks of a run: those a design declares, built from the
// elaborated design rather than by hand (#4956).
class ClockingBlocksOfARun : public VpiDesignRun {};

// A module's default clocking block is reached from it as a clocking block and
// as its default clocking, named as declared and reaching its clocking event.
TEST_F(ClockingBlocksOfARun, ADefaultClockingBlockIsReachedFromItsModule) {
  Run("module top; logic clk, a, b;\n"
      "  default clocking cb @(posedge clk); input a; output b; endclocking\n"
      "endmodule\n");
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  vpiHandle cb = Named(vpiClockingBlock, top, "cb");
  ASSERT_NE(cb, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, cb), "top.cb");
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiDefaultClocking, top)), VpiObjectOf(cb));
  vpiHandle event = vpi_handle(vpiClockingEvent, cb);
  ASSERT_NE(event, nullptr);
  EXPECT_EQ(vpi_get(vpiType, event), vpiEventControl);
}

// A clocking block reaches an io decl per clocking signal, in the order
// declared, each reporting its direction and reaching through vpiExpr the
// signal it is named after (detail 4).
TEST_F(ClockingBlocksOfARun, AClockingBlockReachesItsIoDecls) {
  Run("module top; logic clk, a, b;\n"
      "  clocking cb @(posedge clk); input a; output b; endclocking\n"
      "endmodule\n");
  vpiHandle cb = Named(vpiClockingBlock, By("top"), "cb");
  ASSERT_NE(cb, nullptr);
  EXPECT_EQ(vpi_handle(vpiDefaultClocking, By("top")), nullptr);
  vpiHandle it = vpi_iterate(vpiClockingIODecl, cb);
  ASSERT_NE(it, nullptr);
  vpiHandle a = vpi_scan(it);
  vpiHandle b = vpi_scan(it);
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, a), "a");
  EXPECT_EQ(vpi_get(vpiDirection, a), vpiInput);
  EXPECT_EQ(vpi_get(vpiDirection, b), vpiOutput);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, b)), VpiObjectOf(By("top.b")));
}

// Detail 1: a clocking block reports its default skews' edges and reaches
// their delays; an io decl its own, or, where it writes none, the block's
// default for its direction, its output skew reached as the expression itself.
TEST_F(ClockingBlocksOfARun, SkewsAndEdgesAreTheBlocksDefaultsAndAnIoDeclsOwn) {
  Run("module top; logic clk, a, b, c;\n"
      "  clocking cb @(posedge clk);\n"
      "    default input negedge #2 output #3;\n"
      "    input posedge #1 a; input c; output b;\n"
      "  endclocking\n"
      "endmodule\n");
  vpiHandle cb = Named(vpiClockingBlock, By("top"), "cb");
  ASSERT_NE(cb, nullptr);
  EXPECT_EQ(vpi_get(vpiInputEdge, cb), vpiNegedge);
  EXPECT_EQ(vpi_get(vpiOutputEdge, cb), vpiNoEdge);
  vpiHandle in_skew = vpi_handle(vpiInputSkew, cb);
  ASSERT_NE(in_skew, nullptr);
  EXPECT_EQ(vpi_get(vpiType, in_skew), vpiDelayControl);
  vpiHandle a = Named(vpiClockingIODecl, cb, "a");
  vpiHandle b = Named(vpiClockingIODecl, cb, "b");
  vpiHandle c = Named(vpiClockingIODecl, cb, "c");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(vpi_get(vpiInputEdge, a), vpiPosedge);
  EXPECT_EQ(vpi_get(vpiInputEdge, c), vpiNegedge);
  EXPECT_EQ(vpi_handle(vpiInputSkew, b), nullptr);
  vpiHandle out_skew = vpi_handle(vpiOutputSkew, b);
  ASSERT_NE(out_skew, nullptr);
  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(out_skew, &value);
  EXPECT_EQ(value.value.integer, 3);
}

// A clocking block a generate block declares is each generate block
// instance's, named under it, and not its module's (§37.12).
TEST_F(ClockingBlocksOfARun, AGenerateBlocksClockingBlockIsItsGenScopes) {
  Run("module top; logic clk, a;\n"
      "  for (genvar i = 0; i < 2; i++) begin : g\n"
      "    clocking cb @(posedge clk); input a; endclocking\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(vpi_iterate(vpiClockingBlock, By("top")), nullptr);
  vpiHandle g1 = By("top.g[1]");
  ASSERT_NE(g1, nullptr);
  vpiHandle cb = Named(vpiClockingBlock, g1, "cb");
  ASSERT_NE(cb, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, cb), "top.g[1].cb");
  vpiHandle a = Named(vpiClockingIODecl, cb, "a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, a)), VpiObjectOf(By("top.a")));
}

}  // namespace
}  // namespace delta
