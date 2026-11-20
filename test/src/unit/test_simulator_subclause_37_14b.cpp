#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <utility>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class PortItemsOfARun : public VpiDesignRun {
 protected:
  static vpiHandle Port(const char* inst, const char* name) {
    return Named(vpiPort, By(inst), name);
  }

  static vpiHandle PortAt(const char* inst, std::size_t place) {
    std::vector<vpiHandle> ports = ObjectsOf(vpiPort, By(inst));
    return place < ports.size() ? ports[place] : nullptr;
  }

  static bool Same(vpiHandle a, vpiHandle b) {
    return a != nullptr && b != nullptr && VpiObjectOf(a) == VpiObjectOf(b);
  }

  static int KindOf(vpiHandle obj) {
    return obj == nullptr ? 0 : vpi_get(vpiType, obj);
  }

  static int IntOf(const char* name) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(By(name), &value);
    return value.value.integer;
  }

  static PLI_INT32 PutDelays(vpiHandle obj, unsigned rise, unsigned fall) {
    s_vpi_time times[2] = {};
    times[0].low = rise;
    times[1].low = fall;
    s_vpi_delay delay = {};
    delay.da = times;
    delay.no_of_delays = 2;
    delay.time_type = vpiSimTime;
    vpi_put_delays(obj, &delay);
    s_vpi_error_info info = {};
    PLI_INT32 level = vpi_chk_error(&info);
    return level;
  }

  struct ReadDelays {
    unsigned rise = 0;
    unsigned fall = 0;
    PLI_INT32 level = 0;
  };

  static ReadDelays GetDelays(vpiHandle obj) {
    s_vpi_time times[2] = {};
    s_vpi_delay delay = {};
    delay.da = times;
    delay.no_of_delays = 2;
    delay.time_type = vpiSimTime;
    vpi_get_delays(obj, &delay);
    s_vpi_error_info info = {};
    PLI_INT32 level = vpi_chk_error(&info);
    return {times[0].low, times[1].low, level};
  }

  static PLI_INT32 PutFirstBitDelays(PLI_BYTE8*) {
    std::vector<vpiHandle> bits = ObjectsOf(vpiBit, Port("top.r", "i"));
    if (!bits.empty()) PutDelays(bits[0], 4, 6);
    return 0;
  }

  static void RegisterTask(const char* name, PLI_INT32 (*calltf)(PLI_BYTE8*)) {
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText(name);
    data.calltf = calltf;
    ASSERT_NE(vpi_register_systf(&data), nullptr);
  }
};

using Names = std::vector<std::string>;

constexpr const char* kVectorPorts =
    "module sub(input wire [3:0] a, output logic [1:0] o, inout wire [1:0] b,\n"
    "           input logic s);\n"
    "endmodule\n"
    "module top; wire [3:0] w; wire [1:0] x; wire [1:0] y; wire [7:0] e;\n"
    "  sub u(.a(w), .o(x), .b(y), .s(e));\n"
    "endmodule\n";

TEST_F(PortItemsOfARun, AVectorPortsIndexReachesThatPortBit) {
  Run(kVectorPorts);
  vpiHandle a = Port("top.u", "a");
  ASSERT_NE(a, nullptr);
  vpiHandle bit = vpi_handle_by_index(a, 2);
  ASSERT_NE(bit, nullptr);
  EXPECT_EQ(KindOf(bit), vpiPortBit);
  EXPECT_TRUE(
      Same(vpi_handle(vpiLowConn, bit), vpi_handle_by_index(By("top.u.a"), 2)));
  EXPECT_EQ(vpi_handle_by_index(a, 4), nullptr);
}

TEST_F(PortItemsOfARun, AVectorPortsMultiIndexReachesThatPortBit) {
  Run(kVectorPorts);
  vpiHandle a = Port("top.u", "a");
  ASSERT_NE(a, nullptr);
  PLI_INT32 two[1] = {2};
  vpiHandle bit = vpi_handle_by_multi_index(a, 1, two);
  ASSERT_NE(bit, nullptr);
  EXPECT_EQ(KindOf(bit), vpiPortBit);
  EXPECT_TRUE(
      Same(vpi_handle(vpiLowConn, bit), vpi_handle_by_index(By("top.u.a"), 2)));
  PLI_INT32 four[1] = {4};
  EXPECT_EQ(vpi_handle_by_multi_index(a, 1, four), nullptr);
}

TEST_F(PortItemsOfARun, OutputAndInoutPortsAndTheirBitsReportTheirDirection) {
  Run(kVectorPorts);
  for (const auto& [name, direction] : std::vector<std::pair<const char*, int>>{
           {"o", vpiOutput}, {"b", vpiInout}}) {
    vpiHandle port = Port("top.u", name);
    ASSERT_NE(port, nullptr) << name;
    EXPECT_EQ(vpi_get(vpiDirection, port), direction) << name;
    std::vector<vpiHandle> bits = ObjectsOf(vpiBit, port);
    ASSERT_EQ(bits.size(), 2U) << name;
    for (vpiHandle bit : bits) {
      EXPECT_EQ(vpi_get(vpiDirection, bit), direction) << name;
    }
  }
}

TEST_F(PortItemsOfARun, EveryPortBitReachesItsPortThroughParent) {
  Run(kVectorPorts);
  for (const char* name : {"a", "o", "b"}) {
    vpiHandle port = Port("top.u", name);
    ASSERT_NE(port, nullptr) << name;
    std::vector<vpiHandle> bits = ObjectsOf(vpiBit, port);
    ASSERT_FALSE(bits.empty()) << name;
    for (vpiHandle bit : bits) {
      EXPECT_TRUE(Same(vpi_handle(vpiParent, bit), port)) << name;
    }
  }
}

TEST_F(PortItemsOfARun, APortBitHasNoIndexAndNoName) {
  Run(kVectorPorts);
  for (const char* name : {"a", "o", "b"}) {
    for (vpiHandle bit : ObjectsOf(vpiBit, Port("top.u", name))) {
      EXPECT_EQ(vpi_get(vpiPortIndex, bit), vpiUndefined) << name;
      EXPECT_EQ(vpi_get_str(vpiName, bit), nullptr) << name;
    }
  }
}

TEST_F(PortItemsOfARun, DISABLED_APortBitReachesATypespec) {
  Run(kVectorPorts);
  for (const char* name : {"a", "o", "b"}) {
    std::vector<vpiHandle> bits = ObjectsOf(vpiBit, Port("top.u", name));
    ASSERT_FALSE(bits.empty()) << name;
    for (vpiHandle bit : bits) {
      EXPECT_NE(vpi_handle(vpiTypespec, bit), nullptr) << name;
    }
  }
}

TEST_F(PortItemsOfARun, ScalarAndVectorFollowThePortNotItsConnection) {
  Run("module sub(input logic s, input logic [7:0] v); endmodule\n"
      "module top; wire [7:0] e; wire n; sub u(.s(e), .v(n)); endmodule\n");
  vpiHandle s = Port("top.u", "s");
  vpiHandle v = Port("top.u", "v");
  ASSERT_NE(s, nullptr);
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(vpi_get(vpiScalar, s), 1);
  EXPECT_EQ(vpi_get(vpiVector, s), 0);
  EXPECT_EQ(vpi_get(vpiScalar, v), 0);
  EXPECT_EQ(vpi_get(vpiVector, v), 1);
}

constexpr const char* kNullPorts =
    "module m(a, , b); input a; input [7:0] b; endmodule\n"
    "interface ifn(a, , b); input a; input b; endinterface\n"
    "program prn(a, , b); input a; input b; endprogram\n"
    "module top; wire p; wire [7:0] q;\n"
    "  m u(p, , q); ifn i(p, , p); prn g(p, , p);\n"
    "endmodule\n";

TEST_F(PortItemsOfARun, DISABLED_ANullPortsSizeIsZero) {
  Run(kNullPorts);
  ASSERT_EQ(ObjectsOf(vpiPort, By("top.u")).size(), 3U);
  EXPECT_EQ(vpi_get(vpiSize, PortAt("top.u", 0)), 1);
  EXPECT_EQ(vpi_get(vpiSize, PortAt("top.u", 1)), 0);
  EXPECT_EQ(vpi_get(vpiSize, PortAt("top.u", 2)), 8);
}

TEST_F(PortItemsOfARun, ANullPortHasNoLowerConnectionAndNoName) {
  Run(kNullPorts);
  for (const char* inst : {"top.u", "top.i", "top.g"}) {
    ASSERT_EQ(ObjectsOf(vpiPort, By(inst)).size(), 3U) << inst;
    vpiHandle null_port = PortAt(inst, 1);
    EXPECT_EQ(vpi_handle(vpiLowConn, null_port), nullptr) << inst;
    EXPECT_EQ(vpi_get_str(vpiName, null_port), nullptr) << inst;
  }
}

TEST_F(PortItemsOfARun, ANullPortTakesAPlaceInThePortIndex) {
  Run(kNullPorts);
  ASSERT_EQ(ObjectsOf(vpiPort, By("top.u")).size(), 3U);
  for (int place = 0; place < 3; ++place) {
    EXPECT_EQ(vpi_get(vpiPortIndex, PortAt("top.u", place)), place);
  }
}

TEST_F(PortItemsOfARun, EveryPortIsNumberedByItsPlaceInTheList) {
  Run("module sub(input a, input b, input c); endmodule\n"
      "module rev(b, a); input a; output b; endmodule\n"
      "module top; wire x, y, z; sub u(x, y, z); rev r(y, x); endmodule\n");
  EXPECT_EQ(vpi_get(vpiPortIndex, Port("top.u", "a")), 0);
  EXPECT_EQ(vpi_get(vpiPortIndex, Port("top.u", "b")), 1);
  EXPECT_EQ(vpi_get(vpiPortIndex, Port("top.u", "c")), 2);
  EXPECT_EQ(vpi_get(vpiPortIndex, Port("top.r", "b")), 0);
  EXPECT_EQ(vpi_get(vpiPortIndex, Port("top.r", "a")), 1);
}

TEST_F(PortItemsOfARun, AnUnconnectedPortHasNoHigherConnection) {
  Run("module sub(input a, input b, input c); endmodule\n"
      "interface bus(input logic clk, input logic o); endinterface\n"
      "program prg(input logic clk, input logic o); endprogram\n"
      "module top; wire x, z;\n"
      "  sub n(.a(x), .c(z)); sub p(x, , z);\n"
      "  bus i(.clk(x)); prg g(.clk(x));\n"
      "endmodule\n");
  EXPECT_EQ(vpi_handle(vpiHighConn, Port("top.n", "b")), nullptr);
  EXPECT_EQ(vpi_handle(vpiHighConn, Port("top.p", "b")), nullptr);
  EXPECT_NE(vpi_handle(vpiHighConn, Port("top.p", "c")), nullptr);
  for (const char* inst : {"top.i", "top.g"}) {
    ASSERT_NE(Port(inst, "o"), nullptr) << inst;
    EXPECT_EQ(vpi_handle(vpiHighConn, Port(inst, "o")), nullptr) << inst;
    EXPECT_NE(vpi_handle(vpiHighConn, Port(inst, "clk")), nullptr) << inst;
  }
}

TEST_F(PortItemsOfARun, AnUnnamedExpressionPortHasNoName) {
  Run("module m({a, b}, c[3:0], d); input a, b; input [7:0] c; input d;\n"
      "endmodule\n"
      "module top; wire [1:0] p; wire [3:0] q; wire r; m u(p, q, r);\n"
      "endmodule\n");
  ASSERT_EQ(ObjectsOf(vpiPort, By("top.u")).size(), 3U);
  EXPECT_EQ(vpi_get_str(vpiName, PortAt("top.u", 0)), nullptr);
  EXPECT_EQ(vpi_get_str(vpiName, PortAt("top.u", 1)), nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, PortAt("top.u", 2)), "d");
}

constexpr const char* kInterfaceFormals =
    "interface bus; logic d; modport mp(input d); endinterface\n"
    "module named(bus b); endmodule\n"
    "module viamp(bus.mp t); endmodule\n"
    "module gen(interface s); endmodule\n"
    "module genmp(interface.mp s); endmodule\n"
    "interface outer(bus b, input logic c); endinterface\n"
    "program pp(bus.mp m, input logic c); endprogram\n"
    "module top; bus i(); logic c;\n"
    "  named n(i.mp); named k(i); viamp v(i); gen g(i); genmp h(i.mp);\n"
    "  outer o(i, c); pp p(i, c);\n"
    "endmodule\n";

TEST_F(PortItemsOfARun, AnInterfacePortsTypeIsDecidedByItsFormal) {
  Run(kInterfaceFormals);
  EXPECT_EQ(vpi_get(vpiPortType, Port("top.n", "b")), vpiInterfacePort);
  EXPECT_EQ(vpi_get(vpiPortType, Port("top.g", "s")), vpiInterfacePort);
  EXPECT_EQ(vpi_get(vpiPortType, Port("top.h", "s")), vpiModportPort);
}

TEST_F(PortItemsOfARun, InterfaceAndProgramPortsHaveTheirType) {
  Run(kInterfaceFormals);
  EXPECT_EQ(vpi_get(vpiPortType, Port("top.o", "b")), vpiInterfacePort);
  EXPECT_EQ(vpi_get(vpiPortType, Port("top.o", "c")), vpiPort);
  EXPECT_EQ(vpi_get(vpiPortType, Port("top.p", "m")), vpiModportPort);
  EXPECT_EQ(vpi_get(vpiPortType, Port("top.p", "c")), vpiPort);
}

TEST_F(PortItemsOfARun, EveryInterfacePortsLowerConnectionIsARefObj) {
  Run(kInterfaceFormals);
  for (const auto& [inst, name] :
       std::vector<std::pair<const char*, const char*>>{
           {"top.n", "b"}, {"top.v", "t"}, {"top.g", "s"}, {"top.h", "s"}}) {
    vpiHandle port = Port(inst, name);
    ASSERT_NE(port, nullptr) << inst;
    EXPECT_EQ(KindOf(vpi_handle(vpiLowConn, port)), vpiRefObj) << inst;
  }
}

TEST_F(PortItemsOfARun, InterfaceAndProgramPortsReachBothConnections) {
  Run("interface bus(input logic clk); endinterface\n"
      "program prg(input logic clk); endprogram\n"
      "module top; logic c; bus b(c); prg p(c); endmodule\n");
  for (const char* inst : {"top.b", "top.p"}) {
    vpiHandle clk = Port(inst, "clk");
    ASSERT_NE(clk, nullptr) << inst;
    EXPECT_TRUE(Same(vpi_handle(vpiHighConn, clk), By("top.c"))) << inst;
    EXPECT_TRUE(
        Same(vpi_handle(vpiLowConn, clk), By(std::string(inst) + ".clk")))
        << inst;
  }
}

TEST_F(PortItemsOfARun, APortReachesItsInstanceAndModule) {
  Run("interface bus(input logic clk); endinterface\n"
      "program prg(input logic clk); endprogram\n"
      "module sub(input logic clk); endmodule\n"
      "module top; logic c; bus b(c); prg p(c); sub s(c); endmodule\n");
  for (const char* inst : {"top.b", "top.p", "top.s"}) {
    EXPECT_TRUE(Same(vpi_handle(vpiInstance, Port(inst, "clk")), By(inst)))
        << inst;
  }
  EXPECT_TRUE(Same(vpi_handle(vpiModule, Port("top.s", "clk")), By("top.s")));
}

constexpr const char* kInterfacePortDelays =
    "interface bus; logic d; modport mp(input d); endinterface\n"
    "module sub(bus p, interface q, bus.mp m); endmodule\n"
    "module top; bus i(); sub u(i, i, i.mp); endmodule\n";

TEST_F(PortItemsOfARun, AnInterfacePortTakesNoDelays) {
  Run(kInterfacePortDelays);
  for (const char* name : {"p", "q"}) {
    vpiHandle port = Port("top.u", name);
    ASSERT_NE(port, nullptr) << name;
    EXPECT_EQ(vpi_get(vpiPortType, port), vpiInterfacePort) << name;
    EXPECT_NE(PutDelays(port, 4, 6), 0) << name;
    EXPECT_NE(GetDelays(port).level, 0) << name;
  }
}

TEST_F(PortItemsOfARun, AModportPortTakesDelays) {
  Run(kInterfacePortDelays);
  vpiHandle m = Port("top.u", "m");
  ASSERT_NE(m, nullptr);
  EXPECT_EQ(PutDelays(m, 4, 6), 0);
  ReadDelays read = GetDelays(m);
  EXPECT_EQ(read.level, 0);
  EXPECT_EQ(read.rise, 4U);
  EXPECT_EQ(read.fall, 6U);
}

TEST_F(PortItemsOfARun, APortBitTakesDelaysOfItsOwn) {
  Run("module rcv(input [1:0] i); endmodule\n"
      "module top; wire [1:0] w; rcv r(w); endmodule\n");
  std::vector<vpiHandle> bits = ObjectsOf(vpiBit, Port("top.r", "i"));
  ASSERT_EQ(bits.size(), 2U);
  EXPECT_EQ(PutDelays(bits[0], 4, 6), 0);
  ReadDelays first = GetDelays(bits[0]);
  EXPECT_EQ(first.level, 0);
  EXPECT_EQ(first.rise, 4U);
  EXPECT_EQ(first.fall, 6U);
  ReadDelays second = GetDelays(bits[1]);
  EXPECT_EQ(second.rise, 0U);
  EXPECT_EQ(second.fall, 0U);
}

TEST_F(PortItemsOfARun, DISABLED_OnlyTheBitGivenDelaysTakesThem) {
  RegisterTask("$bit_delays", &PutFirstBitDelays);
  Run("module rcv(input [1:0] i); timeunit 1ns; timeprecision 1ns;\n"
      "  int hi, lo;\n"
      "  always @(i[1]) if (i[1] === 1'b1) hi = $time;\n"
      "  always @(i[0]) if (i[0] === 1'b1) lo = $time;\n"
      "endmodule\n"
      "module top; timeunit 1ns; timeprecision 1ns;\n"
      "  logic [1:0] a = 0; wire [1:0] w; assign w = a; rcv r(w);\n"
      "  initial begin #1 $bit_delays; #9 a = 2'b11; #10; end\n"
      "endmodule\n");
  EXPECT_EQ(IntOf("top.r.hi"), 14);
  EXPECT_EQ(IntOf("top.r.lo"), 10);
}

}  // namespace
}  // namespace delta
