#include "fixture_simulator.h"
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

}  // namespace
