// §23.9 "Scope rules" lists Modules first among the elements that define a new
// scope, and fixes where a direct (non-hierarchical) reference is allowed to
// look: "If it is declared locally, then the local shall be used; if not, the
// search shall continue upward until an item by that name is found or until a
// module, interface, program, or checker boundary is encountered. If the item
// is a variable, it shall stop at a module boundary". Example 1 restates the
// limit for Figure 23-2: "The scope available to upward searching extends
// outward to all containing rectangles -- with the boundary of the module A as
// the outer limit."
//
// This file covers that rule for the identifiers inside a *declaration
// initializer* of a variable declared in an instantiated module: `int q = P;`
// in a child must read the child instance's own `P`, and `logic [7:0] b = a;`
// must read the child's own `a` whether or not the top declares one.
//
// The ten UpwardNameReferenceSimulation cases in
// test/src/unit/test_simulator_subclause_23_08.cpp resolve names from inside an
// `initial` block of an instantiated module. A procedural read runs with
// SimContext::current_process_ set to a Process carrying its instance prefix,
// so those cases exercise a resolution path that already takes the instance
// into account and say nothing about the declaration-initializer path, where
// the initializer is evaluated during lowering with no process running. Every
// case here therefore declares the initializer in the child's body and reads
// the result back through the instance prefix, without an `initial` block on
// the child side.
//
// Every case holds distinct nonzero values on the two sides of the module
// boundary, because docs/tenets/tests/UNIT_TESTS.md rules that an input that
// cannot fail proves nothing: a child and a top holding the same value -- or a
// pair of 4-state variables both left at x -- yield the answer §23.9 requires
// even when the initializer read the wrong scope.

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// A parameter is the item §23.9 protects most sharply, because a parameter is
// instance-specific: `child #(.P(7)) u1();` gives u1 its own P, and the local
// P is what "if it is declared locally, then the local shall be used" names.
// No existing case initializes a child's variable from that child's own
// parameter; UpwardParameterReferenceSimulation reads `parent.P` by
// hierarchical path from an `initial` block, which is neither a direct
// reference nor a declaration initializer.
TEST(InstanceScopeSimulation, ChildInitializerReadsOwnInstanceParameter) {
  SimFixture f;
  auto* q = RunAndFindVar(
      "module child #(parameter int P = 0);\n"
      "  int q = P;\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.P(7)) u1();\n"
      "endmodule\n",
      f, "u1.q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 7u);
}

// The consequence §23.9 forces and no other case observes: two instances of one
// module must initialize from their own overrides, so u1.q and u2.q must
// differ. A single-instance case cannot catch a resolution that ignores the
// instance entirely, because with one instance there is only one answer to
// give; this one fails whenever both copies are initialized from the same
// scope, whatever value that scope holds.
TEST(InstanceScopeSimulation,
     TwoInstancesInitializeFromTheirOwnParameterOverride) {
  SimFixture f;
  auto* q1 = RunAndFindVar(
      "module child #(parameter int P = 0);\n"
      "  int q = P;\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.P(7)) u1();\n"
      "  child #(.P(9)) u2();\n"
      "endmodule\n",
      f, "u1.q");
  ASSERT_NE(q1, nullptr);
  auto* q2 = f.ctx.FindVariable("u2.q");
  ASSERT_NE(q2, nullptr);
  EXPECT_EQ(q1->value.ToUint64(), 7u);
  EXPECT_EQ(q2->value.ToUint64(), 9u);
}

// "If it is declared locally, then the local shall be used" -- the child
// declares its own `a`, so the search must not leave the child at all, even
// though the top declares a variable of the same name that is already
// initialized by the time the child's declarations are lowered. 0xA5 and 0x3C
// share no bits that would let a wrong read pass, and both are nonzero so
// neither can be confused with an unresolved identifier's zero.
TEST(InstanceScopeSimulation,
     ChildInitializerPrefersOwnDeclarationOverTopSameName) {
  SimFixture f;
  auto* b = RunAndFindVar(
      "module child;\n"
      "  logic [7:0] a = 8'hA5;\n"
      "  logic [7:0] b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] a = 8'h3C;\n"
      "  child u1();\n"
      "endmodule\n",
      f, "u1.b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.ToUint64(), 0xA5u);
}

// The same child under a top that declares no `a` at all. This separates the
// two ways the rule can be broken, which the case above cannot tell apart: a
// search that walks past the module boundary lands on the top's `a` when the
// top has one, and on nothing when it does not. Only the absent-declaration
// form shows that the child's own `a` was never consulted, since the answer
// then is neither of the two declared values.
TEST(InstanceScopeSimulation,
     ChildInitializerWithNoTopDeclarationReadsOwnVariable) {
  SimFixture f;
  auto* b = RunAndFindVar(
      "module child;\n"
      "  logic [7:0] a = 8'hA5;\n"
      "  logic [7:0] b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  child u1();\n"
      "endmodule\n",
      f, "u1.b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.ToUint64(), 0xA5u);
}

// An event initializer names the aliased event by a direct reference, so §23.9
// governs it exactly as it governs a value initializer, and the alias is
// observable as pointer identity rather than as a number. No existing case
// aliases an event inside an instance:
// Simulator.EventAliasInitializerSharesSyncObject in
// test/src/unit/test_simulator_subclause_06_17.cpp declares both events in the
// top module, where there is no boundary to cross. The top's own `e1` is the
// wrong target this case rules out, and pointer identity distinguishes it from
// the child's `e1` however either event behaves at run time.
TEST(InstanceScopeSimulation, ChildEventInitializerAliasesOwnInstanceEvent) {
  SimFixture f;
  auto* e2 = RunAndFindVar(
      "module child;\n"
      "  event e1;\n"
      "  event e2 = e1;\n"
      "endmodule\n"
      "module top;\n"
      "  event e1;\n"
      "  child u1();\n"
      "endmodule\n",
      f, "u1.e2");
  ASSERT_NE(e2, nullptr);
  auto* e1 = f.ctx.FindVariable("u1.e1");
  ASSERT_NE(e1, nullptr);
  EXPECT_EQ(e2, e1);
}

// `new[n](src)` names its source array by a direct reference too, and a dynamic
// array is stored as a queue rather than as a Variable, so it is resolved by a
// different lookup than every case above.
// DynamicArrayNewSimulation.DeclNewWithInitCopiesElements in
// test/src/unit/test_simulator_subclause_07_05_01.cpp declares both arrays in
// the top module, so no case reaches the copy source across a module boundary.
// The two source arrays hold disjoint nonzero elements, so element 0 alone says
// which array was copied.
TEST(InstanceScopeSimulation, ChildDynArrayNewCopiesFromOwnInstanceSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child;\n"
      "  int src[] = '{4, 5};\n"
      "  int dst[] = new[2](src);\n"
      "endmodule\n"
      "module top;\n"
      "  int src[] = '{1, 2};\n"
      "  child u1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* dst = f.ctx.FindQueue("u1.dst");
  ASSERT_NE(dst, nullptr);
  ASSERT_FALSE(dst->elements.empty());
  EXPECT_EQ(dst->elements[0].ToUint64(), 4u);
}

}  // namespace
