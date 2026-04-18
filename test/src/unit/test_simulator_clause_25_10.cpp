#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(InterfaceObjectAccessSim,
     HierarchicalWriteDrivesUnderlyingInterfaceSignal) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface ebus_i;\n"
      "  integer I;\n"
      "endinterface\n"
      "module top;\n"
      "  ebus_i ebus();\n"
      "  initial top.ebus.I = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* signal = f.ctx.FindVariable("top.ebus.I");
  ASSERT_NE(signal, nullptr);
  EXPECT_EQ(signal->value.ToUint64(), 42u);
}

TEST(InterfaceObjectAccessSim,
     HierarchicalWriteBypassesModportBoundChildConnection) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface ebus_i;\n"
      "  integer I;\n"
      "  logic Q;\n"
      "  modport mp(input Q);\n"
      "endinterface\n"
      "module sub(ebus_i.mp i);\n"
      "endmodule\n"
      "module top;\n"
      "  ebus_i ebus();\n"
      "  sub s1(ebus.mp);\n"
      "  initial top.ebus.I = 7;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* signal = f.ctx.FindVariable("top.ebus.I");
  ASSERT_NE(signal, nullptr);
  EXPECT_EQ(signal->value.ToUint64(), 7u);
}

TEST(InterfaceObjectAccessSim,
     PortMemberReadReturnsUnderlyingInterfaceSignalValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface ebus_i;\n"
      "  integer Q;\n"
      "  modport mp(input Q);\n"
      "endinterface\n"
      "module sub(ebus_i.mp i);\n"
      "  integer observed;\n"
      "  initial observed = i.Q;\n"
      "endmodule\n"
      "module top;\n"
      "  ebus_i ebus();\n"
      "  sub s1(ebus.mp);\n"
      "  initial ebus.Q = 99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* observed = f.ctx.FindVariable("top.s1.observed");
  ASSERT_NE(observed, nullptr);
  EXPECT_EQ(observed->value.ToUint64(), 99u);
}

TEST(InterfaceObjectAccessSim,
     PortMemberReadOfInterfaceLocalparamReturnsConstantValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface ebus_i;\n"
      "  localparam True = 5;\n"
      "  logic Q;\n"
      "  modport mp(input Q);\n"
      "endinterface\n"
      "module sub(ebus_i.mp i);\n"
      "  integer observed;\n"
      "  initial observed = i.True;\n"
      "endmodule\n"
      "module top;\n"
      "  ebus_i ebus();\n"
      "  sub s1(ebus.mp);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* observed = f.ctx.FindVariable("top.s1.observed");
  ASSERT_NE(observed, nullptr);
  EXPECT_EQ(observed->value.ToUint64(), 5u);
}

}  // namespace
