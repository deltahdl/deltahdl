
#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(DefaultPortValueSimulation, OmittedInputUsesDefaultNamedConn) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic [7:0] a = 8'hFF, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.b(result));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

TEST(DefaultPortValueSimulation, ExplicitConnectionOverridesDefault) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic [7:0] a = 8'hFF, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.a(8'h42), .b(result));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x42u);
}

TEST(DefaultPortValueSimulation, OrderedOmissionUsesDefault) {
  // §23.2.2.4: the general rule is that an input port with a default may be
  // omitted from the instantiation and the compiler inserts the default -- the
  // subclause's own worked example uses positional (ordered) instances with a
  // trailing input left off. The named-connection form is covered separately;
  // this exercises the ordered form. Here datain is the trailing port and is
  // omitted, so the child observes the declared default 8'hA5 and drives it
  // out.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(output logic [7:0] dataout,\n"
      "             input logic [7:0] datain = 8'hA5);\n"
      "  assign dataout = datain;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(result);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xA5u);
}

TEST(DefaultPortValueSimulation, DefaultFromLocalparamConstant) {
  // §23.2.2.4: a port default is a constant expression evaluated in the
  // defining module's scope. A literal and a compilation-unit parameter are
  // covered elsewhere; this covers the localparam form, which reaches the value
  // through a different declaration/resolution path (a localparam declared in
  // the child's own parameter port list). The default references W, so omitting
  // datain must drive W's value 8'h3C.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child #(localparam logic [7:0] W = 8'h3C) (\n"
      "  output logic [7:0] dataout,\n"
      "  input logic [7:0] datain = W);\n"
      "  assign dataout = datain;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.dataout(result));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x3Cu);
}

TEST(DefaultPortValueSimulation, DefaultEvaluatedInDefiningModuleScope) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "parameter logic [7:0] My_DataIn = 8'hFF;\n"
      "module bus_conn (\n"
      "  output logic [7:0] dataout,\n"
      "  input        [7:0] datain = My_DataIn\n"
      ");\n"
      "  assign dataout = datain;\n"
      "endmodule\n"
      "module top;\n"
      "  parameter logic [7:0] My_DataIn = 8'h00;\n"
      "  logic [7:0] result;\n"
      "  bus_conn u(.dataout(result));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

}  // namespace
