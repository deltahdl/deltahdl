#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(EnumerationSimulation, DefaultIntBaseTypeWidthAtRuntime) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module top;\n"
      "  enum {IDLE, BUSY, DONE} state;\n"
      "  int observed;\n"
      "  initial begin\n"
      "    state = BUSY;\n"
      "    observed = state;\n"
      "  end\n"
      "endmodule\n",
      f, "state");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
}

TEST(EnumerationSimulation, AutoIncrementedValuesPropagateAtRuntime) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module top;\n"
      "  typedef enum {ZERO, ONE, TWO} count_t;\n"
      "  int observed;\n"
      "  initial begin\n"
      "    observed = TWO;\n"
      "  end\n"
      "endmodule\n",
      f, "observed");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

// §6.19: an enum named-constant value is an elaboration-time constant
// expression (§6.20). End-to-end: a value seeded from a real parameter feeds
// the auto-increment cursor and propagates at runtime (A=BASE=10, B=A+1=11).
TEST(EnumerationSimulation, ParameterSeededEnumValuePropagatesAtRuntime) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module top;\n"
      "  parameter int BASE = 10;\n"
      "  enum integer {A = BASE, B} e;\n"
      "  int observed;\n"
      "  initial observed = B;\n"
      "endmodule\n",
      f, "observed");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 11u);
}

// §6.19: "An enumerated type declares a set of integral named constants", and
// Syntax 6-5 places the enum form among the data_type productions, so the
// clause's own example -- `enum {red, yellow, green} light1, light2;` -- gives
// red, yellow and green values without any typedef. Read one back at runtime:
// green is the third member of a zero-based auto-increment, so it is 2.
TEST(EnumerationSimulation, BareEnumDeclarationNamesConstantsAtRuntime) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module top;\n"
      "  enum {red, yellow, green} light1;\n"
      "  int observed;\n"
      "  initial observed = green;\n"
      "endmodule\n",
      f, "observed");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

// §6.19: the same enumeration may be shared by several declarators, as the
// clause's `light1, light2` example is. Its named constants are declared once
// for the enumeration, not once per variable, so the second declarator must
// neither redeclare them nor disturb the values the first gave them.
TEST(EnumerationSimulation, SharedEnumDeclaresItsConstantsOnce) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module top;\n"
      "  enum {red, yellow, green} light1, light2;\n"
      "  int observed;\n"
      "  initial observed = yellow;\n"
      "endmodule\n",
      f, "observed");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §6.19 (printed page 119) has an enumerated type declare its literals as
// named constants of the scope holding the enum, §7.2's Syntax 7-1 (printed
// 146) gives a structure member any data_type, the enum form among them, and
// §23.9's list of scope-defining elements (printed 761) names no structure,
// so IDLE and BUSY are constants of p, read at run time through §26.3's
// package scope resolution operator and by their bare names through the
// wildcard import: 1 * 100 + 1 * 10 + 0 = 110. Before, the package's
// run-time "p.BUSY" constant and the import's backing variable were each
// created for an enumeration written at the top of a typedef alone, and
// `p::BUSY` read 0.
TEST(EnumerationSimulation, StructMemberEnumLiteralOfAPackageReadsAtRuntime) {
  EXPECT_EQ(
      RunAndGet("package p;\n"
                "  typedef struct { enum {IDLE, BUSY} st; int n; } s_t;\n"
                "endpackage\n"
                "module top;\n"
                "  import p::*;\n"
                "  int observed;\n"
                "  initial observed = p::BUSY * 100 + BUSY * 10 + p::IDLE;\n"
                "endmodule\n",
                "observed"),
      110u);
}

// The same for a module's own typedef: the member's enumeration declares A
// and B in the module, numbered from 0 (printed 120), so B * 10 + A is 10.
// Before, `B` was reported an unresolved identifier, the module declaring the
// constants of a typedef naming the enum form alone.
TEST(EnumerationSimulation, StructMemberEnumLiteralOfAModuleReadsAtRuntime) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  typedef struct { enum {A, B} e; int n; } t;\n"
                      "  int observed;\n"
                      "  initial observed = B * 10 + A;\n"
                      "endmodule\n",
                      "observed"),
            10u);
}

// §6.19 (printed page 119) has an enumerated type declare its literals as
// named constants of the scope holding it, and Syntax 6-5 makes the enum form
// a data_type, so p's `enum {X, Y} v;` declares X and Y in p with no typedef,
// and §26.3 (printed 810) makes each a candidate the wildcard import brings
// in: Y * 10 + X is 1 * 10 + 0 = 10. Before, the import's backing variables
// were emitted for a typedef's enumeration alone, so Y had no storage in the
// module and read nothing.
TEST(EnumerationSimulation, PackageBareEnumLiteralReadsThroughAWildcardImport) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  enum {X, Y} v;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p::*;\n"
                      "  int observed;\n"
                      "  initial observed = Y * 10 + X;\n"
                      "endmodule\n",
                      "observed"),
            10u);
}

// §3.12.1 (printed page 56) has the compilation-unit scope hold any item a
// package holds, a data declaration among them, visible to the modules of
// the unit written after it; §6.19 (printed 119) has an enumerated type
// declare its literals as constants of the scope holding it, Syntax 6-5
// making the enum form a data_type, so a unit-scope `enum {X, Y} v;`
// declares X and Y with no typedef, and the module reads Y * 10 + X as
// 1 * 10 + 0 = 10 at run time through the backing variables
// RegisterCuEnumLiterals gives it. Before, the parser admitted no enum head
// to a unit-scope data declaration (IsCuScopeDataTypeKeyword), reporting
// "expected top-level declaration", and RegisterCuEnumLiterals gave the
// module the backing variables of a typedef's enumeration alone.
TEST(EnumerationSimulation, UnitScopeBareEnumLiteralReadsAtRuntime) {
  EXPECT_EQ(RunAndGet("enum {X, Y} v;\n"
                      "module top;\n"
                      "  int observed;\n"
                      "  initial observed = Y * 10 + X;\n"
                      "endmodule\n",
                      "observed"),
            10u);
}

// The same clauses for a unit-scope typedef standing beside the bare
// declaration: the typedef's P and Q are declared as before, each enumeration
// numbering its literals from 0 on its own (printed 120), so Q * 10 + P is
// 1 * 10 + 0 = 10 with the bare declaration's X and Y in the same scope. The
// typedef path is the one RegisterCuEnumLiterals walked before f98562dad, and
// this pins it beside the data declaration the walk now reaches too.
TEST(EnumerationSimulation,
     UnitScopeTypedefEnumLiteralReadsBesideABareDeclaration) {
  EXPECT_EQ(RunAndGet("typedef enum {P, Q} t;\n"
                      "enum {X, Y} v;\n"
                      "module top;\n"
                      "  int observed;\n"
                      "  initial observed = Q * 10 + P;\n"
                      "endmodule\n",
                      "observed"),
            10u);
}

}  // namespace
