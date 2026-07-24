
#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ImplicitNamedPortConnectionSimulation, ImplicitInputPropagatesValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] a, b;\n"
      "  assign a = 8'hAB;\n"
      "  child u0(.a, .b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(ImplicitNamedPortConnectionSimulation, MixedImplicitAndExplicitPropagate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic [7:0] a, input logic [7:0] b,\n"
      "             output logic [7:0] c);\n"
      "  assign c = a + b;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] a, c;\n"
      "  assign a = 8'd10;\n"
      "  child u0(.a, .b(8'd20), .c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("c");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

TEST(ImplicitNamedPortConnectionSimulation,
     ImplicitConnectionUsesSignalNotDefault) {
  // 23.3.2.3: an implicit .name connection binds the like-named signal, so the
  // input port's specified default is not used even when one exists. Give the
  // signal a value that differs from the default and observe at run time that
  // the port -- echoed to an output -- carries the signal's value (0x0A), not
  // the default (0xFF). This is the runtime counterpart to the elaborator's
  // structural check that the binding is the signal and not the default.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic [7:0] a = 8'hFF, output logic [7:0] q);\n"
      "  assign q = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] a, q;\n"
      "  assign a = 8'h0A;\n"
      "  child u0(.a, .q);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("q");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x0Au);
}

TEST(ImplicitNamedPortConnectionSimulation,
     ImplicitConnectionPropagatesNetOperand) {
  // 23.3.2.3: the like-named signal an implicit .name binds may be a net rather
  // than a variable. Drive a wire in the instantiating module and observe the
  // value reaching the input port through the implicit connection -- the net
  // operand form of the connection, distinct from the variable operand covered
  // by ImplicitInputPropagatesValue.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic [7:0] a, output logic [7:0] q);\n"
      "  assign q = a;\n"
      "endmodule\n"
      "module top;\n"
      "  wire [7:0] a;\n"
      "  logic [7:0] q;\n"
      "  assign a = 8'h3C;\n"
      "  child u0(.a, .q);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("q");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x3Cu);
}

}  // namespace
