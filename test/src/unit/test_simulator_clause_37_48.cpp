#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.48 Clocking block: a clocking block (vpiClockingBlock) groups the default
// input/output skews, the clocking event, and the clocking io decls
// (vpiClockingIODecl) it contains. These tests observe the production code that
// applies the clause's three numbered "Details" that refine traversal -
// vpiPrefix (detail 2), vpiActual (detail 3), and an io decl's vpiExpr (detail
// 4) - through the same-pipeline public VpiHandleC dispatch. Detail 1 only
// records which construct the skew/edge relations target, and the figure's
// other relations and properties are served by the generic machinery; neither
// refines behavior here.

// The fixture installs a context so the public VpiHandleC entry point runs its
// real dispatch over the test objects.
class ClockingBlock : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// D2: vpiPrefix of a clocking block reaches the virtual interface var the
// clocking block expression is immediately prefixed by. Observed through the
// helper and the public VpiHandleC(vpiPrefix, ...) dispatch. The relation is
// non-NULL exactly because the clocking block carries that prefix.
TEST_F(ClockingBlock, PrefixReachesVirtualInterfacePrefix) {
  VpiObject vif;  // the virtual interface that prefixes the clocking block
  vif.type = vpiVirtualInterfaceVar;

  VpiObject block;
  block.type = vpiClockingBlock;
  block.children = {&vif};

  EXPECT_EQ(VpiClockingBlockPrefix(&block), &vif);
  EXPECT_EQ(VpiHandleC(vpiPrefix, &block), &vif);
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
  EXPECT_EQ(VpiHandleC(vpiPrefix, &block), nullptr);
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
  EXPECT_EQ(VpiHandleC(vpiActual, &block), &resolved);
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
  EXPECT_EQ(VpiHandleC(vpiActual, &block), nullptr);
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
  EXPECT_EQ(VpiHandleC(vpiActual, &block), &resolved);
}

// Figure (clocking io decl -> nets / variables / ref obj): the io-decl expr
// predicate recognizes a ref obj, a net, a reg/logic var, and the variables
// grouping, and rejects an unrelated kind such as a delay control.
TEST_F(ClockingBlock, IODeclExprGroupMembership) {
  EXPECT_TRUE(VpiIsClockingIODeclExprType(vpiRefObj));
  EXPECT_TRUE(VpiIsClockingIODeclExprType(kVpiNet));
  EXPECT_TRUE(VpiIsClockingIODeclExprType(kVpiReg));
  EXPECT_TRUE(VpiIsClockingIODeclExprType(vpiVariables));
  EXPECT_FALSE(VpiIsClockingIODeclExprType(vpiDelayControl));
}

// D4: vpiExpr of a clocking io decl reaches the ref obj the io decl names. This
// is the clause's own example - the io decl "enable" reaches "top.mem1.enable".
// Observed through the helper and the public VpiHandleC(vpiExpr, ...) dispatch.
TEST_F(ClockingBlock, IODeclExprReachesNamedRefObj) {
  VpiObject ref;  // the ref obj "top.mem1.enable" the io decl names
  ref.type = vpiRefObj;

  VpiObject io_decl;
  io_decl.type = vpiClockingIODecl;
  io_decl.children = {&ref};

  EXPECT_EQ(VpiClockingIODeclExpr(&io_decl), &ref);
  EXPECT_EQ(VpiHandleC(vpiExpr, &io_decl), &ref);
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
  EXPECT_EQ(VpiHandleC(vpiExpr, &io_decl), nullptr);
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
}

}  // namespace
}  // namespace delta
