#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.61 Dynamic prefixing: the object model diagram draws a vpiPrefix relation
// from a dynamically prefixed object - a simple expression (a reference or a
// bit-select), a part-select, an indexed part-select, a named event, a named
// event array, or a tf call - to the class var, virtual interface var, or
// clocking block that prefixes it, and gives those source objects one property
// edge, "-> has actual" (bool: vpiHasActual). The clause has three numbered
// Details. Detail 1 fixes when vpiPrefix is non-NULL; detail 2 ties the
// object's memory allocation scheme to a class-var/virtual-interface-var
// prefix; detail 3 fixes what vpiHasActual reports. A tf call's prefix is owned
// by §37.42, so these tests cover only the source kinds and rules §37.61
// defines, observing the production code through the same-pipeline public
// dispatch (vpi_handle and vpi_get) and the clause's helpers.

// The fixture installs a context so the public dispatch entry points run their
// real dispatch over the test objects.
class DynamicPrefixing : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// D1: the source classifier admits exactly the dynamic-prefix source kinds the
// diagram draws vpiPrefix from - a reference and bit-select (the simple
// expression), a part-select and indexed part-select, a named event, and a
// named event array. It rejects a tf call (a method call's prefix is §37.42's)
// and an unrelated kind, so the vpiPrefix traversal is served only where the
// diagram draws it.
TEST_F(DynamicPrefixing, PrefixSourceClassifier) {
  EXPECT_TRUE(VpiIsDynamicPrefixSourceType(vpiRefObj));
  EXPECT_TRUE(VpiIsDynamicPrefixSourceType(vpiBitSelect));
  EXPECT_TRUE(VpiIsDynamicPrefixSourceType(vpiPartSelect));
  EXPECT_TRUE(VpiIsDynamicPrefixSourceType(vpiIndexedPartSelect));
  EXPECT_TRUE(VpiIsDynamicPrefixSourceType(vpiNamedEvent));
  EXPECT_TRUE(VpiIsDynamicPrefixSourceType(vpiNamedEventArray));

  EXPECT_FALSE(VpiIsDynamicPrefixSourceType(vpiMethodFuncCall));
  EXPECT_FALSE(VpiIsDynamicPrefixSourceType(vpiModule));
}

// D1: vpiPrefix of a dynamically prefixed object reaches the object that
// prefixes it. The non-NULL condition spans all three prefix targets the
// diagram draws - a virtual interface var or clocking block prefixing an
// expression, and a class var prefixing a non-static class property - so each
// is exercised through the public vpi_handle(vpiPrefix, ...) dispatch.
TEST_F(DynamicPrefixing, PrefixReachesEachPrefixTargetKind) {
  for (int prefix_kind :
       {vpiClassVar, vpiVirtualInterfaceVar, vpiClockingBlock}) {
    VpiObject prefix;
    prefix.type = prefix_kind;

    VpiObject part_select;  // "all or part of" a prefixed expression
    part_select.type = vpiPartSelect;
    part_select.prefix = &prefix;

    EXPECT_EQ(vpi_handle(vpiPrefix, &part_select), &prefix)
        << "prefix kind " << prefix_kind;
  }
}

// D1: an object that is not prefixed has no prefix, so vpiPrefix reports NULL
// rather than reaching some unrelated child. This is the FALSE side of detail
// 1's non-NULL condition.
TEST_F(DynamicPrefixing, PrefixIsNullWhenObjectIsNotPrefixed) {
  VpiObject child;  // an ordinary child that is not a dynamic prefix
  child.type = vpiOperation;

  VpiObject simple_expr;
  simple_expr.type = vpiRefObj;  // a simple expression, not prefixed
  simple_expr.children = {&child};

  EXPECT_EQ(vpi_handle(vpiPrefix, &simple_expr), nullptr);
}

// D2: an object reached through a class var or virtual interface var prefix
// reports that prefix's memory allocation scheme through
// vpi_get(vpiAllocScheme), not its own. An object without such a prefix reports
// its own scheme.
TEST_F(DynamicPrefixing, AllocSchemeFollowsClassVarAndVifPrefix) {
  for (int prefix_kind : {vpiClassVar, vpiVirtualInterfaceVar}) {
    VpiObject prefix;
    prefix.type = prefix_kind;
    prefix.alloc_scheme = kVpiAutomaticScheme;  // the scheme to be shared

    VpiObject part_select;
    part_select.type = vpiPartSelect;
    part_select.alloc_scheme = kVpiOtherScheme;  // its own scheme, overridden
    part_select.prefix = &prefix;

    EXPECT_EQ(vpi_get(vpiAllocScheme, &part_select), kVpiAutomaticScheme)
        << "prefix kind " << prefix_kind;
  }

  VpiObject unprefixed;
  unprefixed.type = vpiPartSelect;
  unprefixed.alloc_scheme = kVpiDynamicScheme;
  EXPECT_EQ(vpi_get(vpiAllocScheme, &unprefixed), kVpiDynamicScheme);
}

// D2 edge: the shared-scheme rule names only a class var or virtual interface
// var prefix. An object prefixed by a clocking block reports its own allocation
// scheme, so the rule does not over-reach to the third prefix kind.
TEST_F(DynamicPrefixing, AllocSchemeIgnoresClockingBlockPrefix) {
  VpiObject prefix;
  prefix.type = vpiClockingBlock;
  prefix.alloc_scheme = kVpiAutomaticScheme;

  VpiObject part_select;
  part_select.type = vpiPartSelect;
  part_select.alloc_scheme = kVpiOtherScheme;
  part_select.prefix = &prefix;

  EXPECT_EQ(vpi_get(vpiAllocScheme, &part_select), kVpiOtherScheme);
}

// D3 applied through the public dispatch: vpi_get(vpiHasActual) on a source
// object decides the property by the object's provenance and, when that leaves
// it open, by whether an actual is bound at the current simulation time. Every
// condition the clause enumerates is driven here through the production entry
// point. The provenance-pinned cases set a live `actual` that would say the
// opposite, confirming the dispatch forwards both the provenance and the
// current-actual binding into the rule rather than reading the pointer alone.
TEST_F(DynamicPrefixing, HasActualThroughVpiGet) {
  VpiObject actual;  // a corresponding actual at the current simulation time
  actual.type = vpiNamedEvent;

  // Sim-time provenance (the default): the answer tracks the live binding -
  // TRUE when an actual is bound at the current simulation time, FALSE when
  // not.
  VpiObject sim_bound;
  sim_bound.type = vpiNamedEvent;
  sim_bound.actual = &actual;
  EXPECT_EQ(vpi_get(vpiHasActual, &sim_bound), 1);

  VpiObject sim_unbound;
  sim_unbound.type = vpiNamedEvent;
  EXPECT_EQ(vpi_get(vpiHasActual, &sim_unbound), 0);

  // Provenances that always have an actual report TRUE even with no live
  // binding: a statically declared object in an elaborated context, and an
  // automatic variable obtained from a frame (§37.43).
  for (int origin : {kVpiActualStaticElab, kVpiActualFrameVar}) {
    VpiObject obj;
    obj.type = vpiRefObj;
    obj.actual_origin = origin;  // no `actual` bound, yet reports TRUE
    EXPECT_EQ(vpi_get(vpiHasActual, &obj), 1) << "origin " << origin;
  }

  // Provenances that never have an actual report FALSE even when an actual is
  // bound: an object obtained from a class defn lexical context (§37.31), one
  // referenced relative to its class typespec (§37.32), and an automatic
  // variable obtained from a task or function declaration (§37.41).
  for (int origin : {kVpiActualLexicalDefn, kVpiActualClassTypespec,
                     kVpiActualTaskFuncVar}) {
    VpiObject obj;
    obj.type = vpiRefObj;
    obj.actual = &actual;  // bound, yet the provenance pins FALSE
    obj.actual_origin = origin;
    EXPECT_EQ(vpi_get(vpiHasActual, &obj), 0) << "origin " << origin;
  }
}

// D3: vpiHasActual is drawn only on the dynamic-prefix source kinds, so asking
// any other object kind is not a valid query and yields vpiUndefined rather
// than a Boolean answer.
TEST_F(DynamicPrefixing, HasActualIsUndefinedForNonSourceKind) {
  VpiObject module;
  module.type = vpiModule;
  EXPECT_EQ(vpi_get(vpiHasActual, &module), vpiUndefined);
}

}  // namespace
}  // namespace delta
