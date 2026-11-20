#include <gtest/gtest.h>

#include <deque>
#include <string>
#include <string_view>
#include <tuple>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "fixture_simulator.h"
#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class PortContext : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

TEST(PortModel, PortTypeValuesAndFormalDerivation) {
  EXPECT_TRUE(VpiIsValidPortType(vpiPort));
  EXPECT_TRUE(VpiIsValidPortType(vpiInterfacePort));
  EXPECT_TRUE(VpiIsValidPortType(vpiModportPort));
  EXPECT_FALSE(VpiIsValidPortType(vpiRefObj));

  EXPECT_EQ(VpiPortTypeFromFormal(false, false), vpiPort);
  EXPECT_EQ(VpiPortTypeFromFormal(true, false), vpiInterfacePort);
  EXPECT_EQ(VpiPortTypeFromFormal(true, true), vpiModportPort);
}

TEST_F(PortContext, PortTypeReportedThroughVpiGet) {
  VpiObject port;
  port.type = vpiPort;
  port.port_type = vpiModportPort;
  EXPECT_EQ(vpi_get(vpiPortType, VpiHandleOf(&port)), vpiModportPort);
}

TEST(PortModel, DelaysNotApplicableToInterfacePort) {
  EXPECT_FALSE(VpiPortDelaysApplicable(vpiInterfacePort));
  EXPECT_TRUE(VpiPortDelaysApplicable(vpiPort));
  EXPECT_TRUE(VpiPortDelaysApplicable(vpiModportPort));
}

TEST_F(PortContext, GetDelaysOnInterfacePortIsAnError) {
  VpiObject iface_port;
  iface_port.type = vpiPort;
  iface_port.port_type = vpiInterfacePort;

  s_vpi_delay delay = {};
  delay.no_of_delays = 1;
  vpi_get_delays(VpiHandleOf(&iface_port), &delay);
  EXPECT_NE(ctx_.LastError().level, 0);
  ASSERT_NE(ctx_.LastError().message, nullptr);
  EXPECT_NE(std::string(ctx_.LastError().message).find("interface port"),
            std::string::npos);
}

TEST_F(PortContext, HighConnAndLowConnReachDesignatedConnections) {
  VpiObject high, low;
  VpiObject port;
  port.type = vpiPort;
  port.high_conn = &high;
  port.low_conn = &low;
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiHighConn, VpiHandleOf(&port))), &high);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLowConn, VpiHandleOf(&port))), &low);

  VpiObject unconnected;
  unconnected.type = vpiPort;
  unconnected.low_conn = &low;
  EXPECT_EQ(vpi_handle(vpiHighConn, VpiHandleOf(&unconnected)), nullptr);

  VpiObject null_port;
  null_port.type = vpiPort;
  null_port.null_port = true;
  null_port.low_conn = &low;
  EXPECT_EQ(vpi_handle(vpiLowConn, VpiHandleOf(&null_port)), nullptr);
  EXPECT_EQ(VpiLowConn(&null_port), nullptr);
}

TEST(PortModel, InterfacePortLowConnIsRefObj) {
  VpiObject ref_obj;
  ref_obj.type = vpiRefObj;

  VpiObject iface_port;
  iface_port.type = vpiPort;
  iface_port.port_type = vpiInterfacePort;
  iface_port.low_conn = &ref_obj;
  EXPECT_TRUE(VpiPortLowConnSatisfiesInterfaceRule(&iface_port));

  VpiObject net;
  net.type = vpiNet;
  iface_port.low_conn = &net;
  EXPECT_FALSE(VpiPortLowConnSatisfiesInterfaceRule(&iface_port));

  iface_port.low_conn = nullptr;
  EXPECT_FALSE(VpiPortLowConnSatisfiesInterfaceRule(&iface_port));

  VpiObject ordinary;
  ordinary.type = vpiPort;
  ordinary.port_type = vpiPort;
  ordinary.low_conn = &net;
  EXPECT_TRUE(VpiPortLowConnSatisfiesInterfaceRule(&ordinary));
}

TEST_F(PortContext, ScalarAndVectorFollowPortWidth) {
  EXPECT_TRUE(VpiPortScalar(1));
  EXPECT_FALSE(VpiPortScalar(8));
  EXPECT_FALSE(VpiPortVector(1));
  EXPECT_TRUE(VpiPortVector(8));

  VpiObject scalar_port;
  scalar_port.type = vpiPort;
  scalar_port.size = 1;
  EXPECT_EQ(vpi_get(vpiScalar, VpiHandleOf(&scalar_port)), 1);
  EXPECT_EQ(vpi_get(vpiVector, VpiHandleOf(&scalar_port)), 0);

  VpiObject vector_port;
  vector_port.type = vpiPort;
  vector_port.size = 16;
  EXPECT_EQ(vpi_get(vpiScalar, VpiHandleOf(&vector_port)), 0);
  EXPECT_EQ(vpi_get(vpiVector, VpiHandleOf(&vector_port)), 1);
}

TEST_F(PortContext, PortIndexAndNameDoNotApplyToPortBit) {
  EXPECT_TRUE(VpiPortIndexAndNameApply(vpiPort));
  EXPECT_FALSE(VpiPortIndexAndNameApply(vpiPortBit));

  VpiObject port_bit;
  port_bit.type = vpiPortBit;
  port_bit.index = 3;
  port_bit.name = "b";
  EXPECT_EQ(vpi_get(vpiPortIndex, VpiHandleOf(&port_bit)), vpiUndefined);
  EXPECT_EQ(vpi_get_str(vpiName, VpiHandleOf(&port_bit)), nullptr);
}

TEST_F(PortContext, ExplicitNameResolution) {
  EXPECT_STREQ(VpiPortName(true, "exp", "inf"), "exp");
  EXPECT_STREQ(VpiPortName(false, "exp", "inf"), "inf");
  EXPECT_EQ(VpiPortName(false, "", ""), nullptr);
  EXPECT_STREQ(VpiPortName(false, "", "inf"), "inf");

  VpiObject named_port;
  named_port.type = vpiPort;
  named_port.name = "p";
  named_port.explicit_name = true;
  EXPECT_EQ(vpi_get(vpiExplicitName, VpiHandleOf(&named_port)), 1);
  EXPECT_STREQ(vpi_get_str(vpiName, VpiHandleOf(&named_port)), "p");
}

TEST_F(PortContext, PortNameThroughVpiGetStrForInferredAndUnnamed) {
  VpiObject inferred_port;
  inferred_port.type = vpiPort;
  inferred_port.name = "q";
  inferred_port.explicit_name = false;
  EXPECT_EQ(vpi_get(vpiExplicitName, VpiHandleOf(&inferred_port)), 0);
  EXPECT_STREQ(vpi_get_str(vpiName, VpiHandleOf(&inferred_port)), "q");

  VpiObject unnamed_port;
  unnamed_port.type = vpiPort;
  EXPECT_EQ(vpi_get_str(vpiName, VpiHandleOf(&unnamed_port)), nullptr);
}

TEST_F(PortContext, PortIndexGivesDeclarationOrder) {
  VpiObject parent;
  parent.type = vpiModule;
  VpiHandle first = ctx_.CreatePort("a", vpiInput, &parent);
  VpiHandle second = ctx_.CreatePort("b", vpiOutput, &parent);
  VpiHandle third = ctx_.CreatePort("c", vpiInput, &parent);
  EXPECT_EQ(vpi_get(vpiPortIndex, VpiHandleOf(first)), 0);
  EXPECT_EQ(vpi_get(vpiPortIndex, VpiHandleOf(second)), 1);
  EXPECT_EQ(vpi_get(vpiPortIndex, VpiHandleOf(third)), 2);
}

TEST_F(PortContext, NullPortSizeIsZero) {
  EXPECT_EQ(VpiPortSize(true, 8), 0);
  EXPECT_EQ(VpiPortSize(false, 8), 8);

  VpiObject null_port;
  null_port.type = vpiPort;
  null_port.null_port = true;
  null_port.size = 8;
  EXPECT_EQ(vpi_get(vpiSize, VpiHandleOf(&null_port)), 0);

  VpiObject sized_port;
  sized_port.type = vpiPort;
  sized_port.size = 8;
  EXPECT_EQ(vpi_get(vpiSize, VpiHandleOf(&sized_port)), 8);
}

int g_ports_seen = 0;
std::string g_first_port_name;
int g_first_port_index = -1;
int g_first_port_direction = 0;
int g_wide_port_vector = -1;
int g_wide_port_size = 0;
int g_narrow_port_scalar = -1;

PLI_INT32 WalkPortsCalltf(PLI_BYTE8*) {
  vpiHandle mod = vpi_handle_by_name(VpiText("m1"), nullptr);
  if (mod == nullptr) return 0;
  vpiHandle ports = vpi_iterate(vpiPort, mod);
  if (ports == nullptr) return 0;

  for (vpiHandle port = vpi_scan(ports); port != nullptr;
       port = vpi_scan(ports)) {
    ++g_ports_seen;
    const char* name = vpi_get_str(vpiName, port);
    if (g_ports_seen == 1) {
      if (name != nullptr) g_first_port_name = name;
      g_first_port_index = vpi_get(vpiPortIndex, port);
      g_first_port_direction = vpi_get(vpiDirection, port);
    }
    if (name != nullptr && std::string(name) == "b") {
      g_wide_port_vector = vpi_get(vpiVector, port);
      g_wide_port_size = vpi_get(vpiSize, port);
    }
    if (name != nullptr && std::string(name) == "c") {
      g_narrow_port_scalar = vpi_get(vpiScalar, port);
    }
  }
  return 0;
}

void RegisterPortProbe() {
  g_ports_seen = 0;
  g_first_port_name.clear();
  g_first_port_index = -1;
  g_first_port_direction = 0;
  g_wide_port_vector = -1;
  g_wide_port_size = 0;
  g_narrow_port_scalar = -1;

  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$probe");
  data.calltf = &WalkPortsCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

void RunAModuleOfThreePorts(SimFixture& f) {
  auto* design = ElaborateSrc(
      "module m(input a, input [7:0] b, output c);\n"
      "  assign c = a;\n"
      "endmodule\n"
      "module t;\n"
      "  wire p;\n"
      "  wire [7:0] q;\n"
      "  wire r;\n"
      "  m m1(p, q, r);\n"
      "  initial $probe;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
}

class PortModelInARun : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

TEST_F(PortModelInARun, AnInstanceReachesThePortsItDeclares) {
  RegisterPortProbe();

  SimFixture f;
  RunAModuleOfThreePorts(f);

  EXPECT_EQ(g_ports_seen, 3);
  EXPECT_EQ(g_first_port_name, "a");
  EXPECT_EQ(g_first_port_index, 0);
  EXPECT_EQ(g_first_port_direction, vpiInput);
}

TEST_F(PortModelInARun, ThePortsWidthDecidesScalarAndVector) {
  RegisterPortProbe();

  SimFixture f;
  RunAModuleOfThreePorts(f);

  ASSERT_EQ(g_ports_seen, 3);
  EXPECT_EQ(g_wide_port_size, 8);
  EXPECT_EQ(g_wide_port_vector, 1);
  EXPECT_EQ(g_narrow_port_scalar, 1);
}

class PortsOfARun : public VpiDesignRun {
 protected:
  static vpiHandle PortOfU(const char* name) {
    return Named(vpiPort, By("top.u"), name);
  }
};

constexpr const char* kConnectedPorts =
    "module sub(input logic a, output logic o, input logic n);\n"
    "  assign o = a;\n"
    "endmodule\n"
    "module top; logic w, x; wire y; sub u(.a(w & x), .o(y), .n()); "
    "endmodule\n";

TEST_F(PortsOfARun, APortReachesBothOfItsConnections) {
  Run(kConnectedPorts);
  vpiHandle a = PortOfU("a");
  vpiHandle o = PortOfU("o");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(o, nullptr);
  vpiHandle high = vpi_handle(vpiHighConn, a);
  ASSERT_NE(high, nullptr);
  EXPECT_EQ(vpi_get(vpiType, high), vpiOperation);
  EXPECT_EQ(vpi_get(vpiOpType, high), vpiBitAndOp);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLowConn, a)), VpiObjectOf(By("top.u.a")));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiHighConn, o)), VpiObjectOf(By("top.y")));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLowConn, o)), VpiObjectOf(By("top.u.o")));
}

TEST_F(PortsOfARun, AnUnconnectedPortHasNoHigherConnection) {
  Run(kConnectedPorts);
  vpiHandle n = PortOfU("n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(vpi_handle(vpiHighConn, n), nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLowConn, n)), VpiObjectOf(By("top.u.n")));
}

vpiHandle SubInstanceIn(vpiHandle scope) {
  vpiHandle it = scope == nullptr ? nullptr : vpi_iterate(vpiModule, scope);
  while (vpiHandle inst = it == nullptr ? nullptr : vpi_scan(it)) {
    const char* def = vpi_get_str(vpiDefName, inst);
    if (def != nullptr && std::string(def) == "sub") return inst;
  }
  return nullptr;
}

TEST_F(PortsOfARun, AConnectionInAGenerateBlockNamesItsVariable) {
  Run("module sub(input logic a); endmodule\n"
      "module top; logic v;\n"
      "  for (genvar i = 0; i < 1; i++) begin : g logic v; sub u(.a(v)); end\n"
      "endmodule\n");
  vpiHandle inst = SubInstanceIn(By("top.g[0]"));
  if (inst == nullptr) inst = SubInstanceIn(By("top"));
  ASSERT_NE(inst, nullptr);
  vpiHandle a = Named(vpiPort, inst, "a");
  ASSERT_NE(a, nullptr);
  vpiHandle high = vpi_handle(vpiHighConn, a);
  ASSERT_NE(high, nullptr);
  EXPECT_NE(VpiObjectOf(high), VpiObjectOf(By("top.v")));
  EXPECT_STREQ(vpi_get_str(vpiName, high), "v");
}

TEST(PortModel, NoPortSatisfiesTheInterfaceLowConnRule) {
  EXPECT_TRUE(VpiPortLowConnSatisfiesInterfaceRule(nullptr));
}

TEST(PortModel, AnEmptyExplicitNameFallsBackToTheInferredName) {
  EXPECT_STREQ(VpiPortName(true, "", "inf"), "inf");
  EXPECT_EQ(VpiPortName(true, "", ""), nullptr);
}

constexpr const char* kVectorPort =
    "module sub(input wire [3:0] a, input wire s); endmodule\n"
    "module top; wire [3:0] w; wire v; sub u(.a(w), .s(v)); endmodule\n";

TEST_F(PortsOfARun, AVectorPortHoldsAPortBitPerBit) {
  Run(kVectorPort);
  vpiHandle a = PortOfU("a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(KindsOf(vpiBit, a), std::vector<int>(4, vpiPortBit));
  vpiHandle it = vpi_iterate(vpiBit, a);
  ASSERT_NE(it, nullptr);
  vpiHandle first = vpi_scan(it);
  EXPECT_EQ(vpi_get(vpiDirection, first), vpiInput);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLowConn, first)),
            VpiObjectOf(vpi_handle_by_index(By("top.u.a"), 3)));
}

TEST_F(PortsOfARun, AScalarPortHoldsNoPortBits) {
  Run(kVectorPort);
  vpiHandle s = PortOfU("s");
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(vpi_iterate(vpiBit, s), nullptr);
}

TEST(PortModel, PortBitsAreMadeFromTheLowConnsBits) {
  std::deque<VpiObject> made;
  std::deque<std::string> kept;
  Arena arena;
  const VpiAttachBuild kBuild{[&made] { return &made.emplace_back(); },
                              [&kept](std::string name) {
                                kept.push_back(std::move(name));
                                return std::string_view(kept.back());
                              },
                              arena};
  VpiObject unconnected;
  unconnected.type = vpiPort;
  VpiMakePortBits(&unconnected, kBuild);
  EXPECT_TRUE(unconnected.children.empty());

  VpiObject index;
  index.type = vpiConstant;
  VpiObject bit;
  bit.type = vpiNetBit;
  bit.index = 1;
  bit.bit_offset = 1;
  VpiObject net;
  net.type = vpiNet;
  net.children = {&index, &bit};
  VpiObject port;
  port.type = vpiPort;
  port.direction = vpiInput;
  port.low_conn = &net;
  VpiMakePortBits(&port, kBuild);
  ASSERT_EQ(port.children.size(), 1U);
  EXPECT_EQ(port.children[0]->type, vpiPortBit);
  EXPECT_EQ(port.children[0]->low_conn, &bit);
  EXPECT_EQ(port.children[0]->index, 1);
  EXPECT_EQ(port.children[0]->direction, vpiInput);
}

TEST_F(PortsOfARun, AVariablePortHoldsAPortBitPerBit) {
  Run("module sub(output logic [1:0] o); endmodule\n"
      "module top; wire [1:0] x; sub u(.o(x)); endmodule\n");
  EXPECT_EQ(KindsOf(vpiBit, By("top.u.o")), std::vector<int>(2, vpiRegBit));
  vpiHandle o = PortOfU("o");
  ASSERT_NE(o, nullptr);
  EXPECT_EQ(KindsOf(vpiBit, o), std::vector<int>(2, vpiPortBit));
}

TEST_F(PortContext, APortBitReachesItsPortThroughParent) {
  VpiObject port;
  port.type = vpiPort;
  VpiObject bit;
  bit.type = vpiPortBit;
  bit.parent = &port;
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, VpiHandleOf(&bit))), &port);
}

TEST_F(PortsOfARun, APortsTypeFollowsItsFormal) {
  Run("interface bus; logic d; modport mp(input d); endinterface\n"
      "module sub(bus b, bus.mp m, input logic a); endmodule\n"
      "module top; bus i(); sub u(.b(i), .m(i), .a(1'b0)); endmodule\n");
  for (const auto& [name, type] : std::vector<std::pair<const char*, int>>{
           {"b", vpiInterfacePort}, {"m", vpiModportPort}, {"a", vpiPort}}) {
    vpiHandle port = PortOfU(name);
    ASSERT_NE(port, nullptr) << name;
    EXPECT_EQ(vpi_get(vpiPortType, port), type) << name;
  }
  EXPECT_EQ(vpi_handle(vpiTypespec, PortOfU("b")), nullptr);
}

TEST_F(PortsOfARun, APortWrittenWithItsOwnNameIsExplicitlyNamed) {
  Run("module sub(.q(c), .p(a), b); input c; input [3:0] a; input b;\n"
      "endmodule\n"
      "module top; wire [3:0] w; wire v; sub u(.q(v), .p(w), .b(v));\n"
      "endmodule\n");
  vpiHandle p = PortOfU("p");
  vpiHandle b = PortOfU("b");
  ASSERT_NE(p, nullptr);
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(vpi_get(vpiExplicitName, p), 1);
  EXPECT_EQ(vpi_get(vpiExplicitName, b), 0);
  vpiHandle typespec = vpi_handle(vpiTypespec, p);
  ASSERT_NE(typespec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, typespec), vpiLogicTypespec);
  const std::vector<vpiHandle> kRanges = ObjectsOf(vpiRange, typespec);
  ASSERT_EQ(kRanges.size(), 1U);
  EXPECT_EQ(vpi_get(vpiSize, kRanges[0]), 4);
}

TEST_F(PortsOfARun, APortWrittenAsAnExpressionReachesATypespecOfItsWidth) {
  Run("module sub(output .p(r[3:1]), output .q(r[0]), output .c({x, y}),\n"
      "           output .s(v));\n"
      "  logic [7:0] r; logic x; logic [1:0] y; logic [2:0] v;\n"
      "endmodule\n"
      "module top; wire [2:0] a, c, d; wire b;\n"
      "  sub u(.p(a), .q(b), .c(c), .s(d));\n"
      "endmodule\n");
  for (const auto& [name, size] : std::vector<std::pair<const char*, int>>{
           {"p", 3}, {"q", 0}, {"c", 3}, {"s", 3}}) {
    ASSERT_NE(PortOfU(name), nullptr) << name;
    vpiHandle typespec = vpi_handle(vpiTypespec, PortOfU(name));
    ASSERT_NE(typespec, nullptr) << name;
    EXPECT_EQ(vpi_get(vpiType, typespec), vpiLogicTypespec) << name;
    const std::vector<vpiHandle> kRanges = ObjectsOf(vpiRange, typespec);
    ASSERT_EQ(kRanges.size(), size == 0 ? 0U : 1U) << name;
    if (size != 0) EXPECT_EQ(vpi_get(vpiSize, kRanges[0]), size) << name;
  }
}

TEST_F(PortsOfARun, APortConnectedByNameSaysSo) {
  Run("module sub(input logic a, input logic b); endmodule\n"
      "module top; logic a, b;\n"
      "  sub u(.a(a), .b()); sub v(a, b); sub z(.*);\n"
      "endmodule\n");
  const std::vector<std::tuple<const char*, const char*, int>> kExpected{
      {"top.u", "a", 1}, {"top.u", "b", 0}, {"top.v", "a", 0},
      {"top.v", "b", 0}, {"top.z", "a", 1}, {"top.z", "b", 1}};
  for (const auto& [inst, name, by_name] : kExpected) {
    vpiHandle port = Named(vpiPort, By(inst), name);
    ASSERT_NE(port, nullptr) << inst << "." << name;
    EXPECT_EQ(vpi_get(vpiConnByName, port), by_name) << inst << "." << name;
  }
}

TEST_F(PortsOfARun, ARefPortsDirectionIsRef) {
  Run("module sub(ref int r, input var int i); endmodule\n"
      "module top; int x, y; sub u(.r(x), .i(y)); endmodule\n");
  vpiHandle r = PortOfU("r");
  vpiHandle i = PortOfU("i");
  ASSERT_NE(r, nullptr);
  ASSERT_NE(i, nullptr);
  EXPECT_EQ(vpi_get(vpiDirection, r), vpiRef);
  EXPECT_EQ(vpi_get(vpiDirection, i), vpiInput);
}

int TypespecKindOf(vpiHandle port) {
  vpiHandle typespec = vpi_handle(vpiTypespec, port);
  return typespec == nullptr ? 0 : vpi_get(vpiType, typespec);
}

TEST_F(PortsOfARun, APortReachesTheTypespecOfItsType) {
  Run("typedef logic [3:0] nib_t;\n"
      "module sub #(parameter W = 2, parameter type T = int)\n"
      "  (input nib_t a, input var int b, input logic [1:0] c [2],\n"
      "   output byte d, input e, input logic [W-1:0] f, input var T g);\n"
      "endmodule\n"
      "module loc(h); typedef bit [5:0] six_t; input six_t h; endmodule\n"
      "module top; nib_t w; int x; logic [1:0] y [2]; byte z; wire q;\n"
      "  logic [3:0] r; shortint s; bit [5:0] t;\n"
      "  sub #(.W(4), .T(shortint)) u(w, x, y, z, q, r, s);\n"
      "  loc l(t);\n"
      "endmodule\n");
  vpiHandle a = vpi_handle(vpiTypespec, PortOfU("a"));
  ASSERT_NE(a, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, a), "nib_t");
  EXPECT_EQ(TypespecKindOf(PortOfU("b")), vpiIntTypespec);
  EXPECT_EQ(TypespecKindOf(PortOfU("c")), vpiArrayTypespec);
  EXPECT_EQ(TypespecKindOf(PortOfU("d")), vpiByteTypespec);
  EXPECT_EQ(TypespecKindOf(PortOfU("e")), vpiLogicTypespec);
  EXPECT_EQ(vpi_handle_by_index(PortOfU("e"), 0), nullptr);
  vpiHandle f = vpi_handle(vpiTypespec, PortOfU("f"));
  ASSERT_NE(f, nullptr);
  EXPECT_EQ(vpi_get(vpiType, f), vpiLogicTypespec);
  const std::vector<vpiHandle> kRanges = ObjectsOf(vpiRange, f);
  ASSERT_EQ(kRanges.size(), 1U);
  EXPECT_EQ(vpi_get(vpiSize, kRanges[0]), 4);
  EXPECT_EQ(TypespecKindOf(PortOfU("g")), vpiShortIntTypespec);
  vpiHandle h = vpi_handle(vpiTypespec, Named(vpiPort, By("top.l"), "h"));
  ASSERT_NE(h, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, h), "six_t");
}

TEST_F(PortsOfARun, APortOverTwoStateObjectsReachesABitTypespec) {
  Run("module sub(output .p({x, y}), output .q(n[1:0]), output .s(y[1]),\n"
      "           output .t({x, v}));\n"
      "  bit x; bit [1:0] y; wire [2:0] n; logic [2:0] v;\n"
      "endmodule\n"
      "module top; wire [2:0] a; wire [1:0] b; wire c; wire [3:0] d;\n"
      "  sub u(.p(a), .q(b), .s(c), .t(d));\n"
      "endmodule\n");
  for (const auto& [name, kind] :
       std::vector<std::pair<const char*, int>>{{"p", vpiBitTypespec},
                                                {"q", vpiLogicTypespec},
                                                {"s", vpiBitTypespec},
                                                {"t", vpiLogicTypespec}}) {
    ASSERT_NE(PortOfU(name), nullptr) << name;
    EXPECT_EQ(TypespecKindOf(PortOfU(name)), kind) << name;
  }
}

TEST_F(PortsOfARun, ANestedModulesPortReachesItsTypespec) {
  Run("module top; logic [2:0] w;\n"
      "  module inner(input logic [2:0] p); endmodule\n"
      "  inner u(.p(w));\n"
      "endmodule\n");
  vpiHandle typespec = vpi_handle(vpiTypespec, PortOfU("p"));
  ASSERT_NE(typespec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, typespec), vpiLogicTypespec);
}

}  // namespace
}  // namespace delta
