// A.10 item 2: "It shall be illegal to initialize a port that is not a
// variable output port", so a variable output port with `= constant_expression`
// is initialized, as §23.2.2.2's Syntax 23-4 writes it. These cases observe
// the initializer reaching the port variable of the top module and of a child
// instance, and the parent reading the child's initial value through the
// connection.

#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// The top module's own output port variable holds its initializer, and the
// initial procedure reads it, §6.8 having the initialization happen "before
// any initial or always procedures are started".
TEST(PortInitializerSimulation, TopOutputPortHoldsItsInitializer) {
  SimFixture f;
  auto out = RunCapture(
      "module m(output logic [3:0] q = 4'd9);\n"
      "  initial $display(\"q=%0d\", q);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "q=9\n");
}

// A parameter of the module the port is declared in is what the constant
// expression reads, and the value the port starts with is the one the
// expression folds to in that scope.
TEST(PortInitializerSimulation, InitializerReadsTheModulesOwnParameter) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m #(parameter int START = 6) (output int q = START + 1);\n"
      "endmodule\n",
      f, "q");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

// A child instance's initialized output port starts at its initializer, and
// the parent's net connected to it reads that value once the run has settled,
// while an output port left unconnected is still initialized.
TEST(PortInitializerSimulation, ChildOutputPortInitializerReachesTheParent) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(output logic [7:0] q = 8'h5A, output logic [7:0] r = "
      "8'h3);\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] seen;\n"
      "  child u(.q(seen), .r());\n"
      "endmodule\n",
      f, "seen");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x5Au);
  auto* r = f.ctx.FindVariable("u.r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 3u);
}

}  // namespace
