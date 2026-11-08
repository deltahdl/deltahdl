#include <gtest/gtest.h>

#include <algorithm>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/types.h"
#include "elaborator/rtlir.h"
#include "fixture_vpi_run.h"
#include "parser/ast_type.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class ArrayNetsOfARun : public VpiDesignRun {
 protected:
  static int IntOf(vpiHandle obj) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(obj, &value);
    return value.value.integer;
  }

  static vpiHandle Array() { return By("top.n"); }
};

constexpr const char* kArrayNet =
    "module top; wire [3:0] n [0:2]; assign n[1] = 4'b1010; endmodule\n";

TEST_F(ArrayNetsOfARun, ANetWithAnUnpackedDimensionIsAnArrayNet) {
  Run(kArrayNet);
  EXPECT_EQ(vpi_get(vpiType, Array()), vpiNetArray);
}

TEST_F(ArrayNetsOfARun, AnArrayNetsSizeIsTheNumberOfItsNets) {
  Run(kArrayNet);
  EXPECT_EQ(vpi_get(vpiSize, Array()), 3);
}

TEST_F(ArrayNetsOfARun, EachNetOfAnArrayNetIsAnArrayMember) {
  Run(kArrayNet);
  vpiHandle element = vpi_handle_by_index(Array(), 1);
  ASSERT_NE(element, nullptr);
  EXPECT_EQ(vpi_get(vpiType, element), vpiNet);
  EXPECT_EQ(vpi_get(vpiArrayMember, element), 1);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, element)), VpiObjectOf(Array()));
}

TEST_F(ArrayNetsOfARun, TheArrayNetHoldsItsNetsInPlaceOfTheModule) {
  Run(kArrayNet);
  EXPECT_EQ(NamesOf(vpiNetArray, By("top")), std::vector<std::string>{"n"});
  EXPECT_TRUE(NamesOf(vpiNet, By("top")).empty());
  EXPECT_EQ(NamesOf(vpiNet, Array()),
            (std::vector<std::string>{"n[0]", "n[1]", "n[2]"}));
}

TEST_F(ArrayNetsOfARun, TheBitsAreTheArrayNetsNets) {
  Run(kArrayNet);
  vpiHandle element = vpi_handle_by_index(Array(), 1);
  ASSERT_NE(element, nullptr);
  EXPECT_EQ(IntOf(element), 0b1010);
  EXPECT_EQ(IntOf(vpi_handle_by_index(element, 1)), 1);
  EXPECT_EQ(vpi_iterate(vpiBit, Array()), nullptr);
}

class NetKindsOfARun : public VpiDesignRun {
 protected:
  static int KindOf(const char* name) { return vpi_get(vpiType, By(name)); }

  static int TypespecKindOf(const char* name) {
    vpiHandle typespec = vpi_handle(vpiTypespec, By(name));
    return typespec != nullptr ? vpi_get(vpiType, typespec) : 0;
  }
};

constexpr const char* kNetDataTypes =
    "module top;\n"
    "  typedef enum logic [1:0] {A, B} e_t;\n"
    "  typedef struct packed { logic a; logic b; } s_t;\n"
    "  nettype int int_net;\n"
    "  nettype bit [3:0] bit_net;\n"
    "  wire w; wire logic [3:0] l; wire integer i; wire time t;\n"
    "  wire e_t e; wire enum logic {C, D} f; wire s_t [1:0] p;\n"
    "  int_net n; bit_net b;\n"
    "endmodule\n";

TEST_F(NetKindsOfARun, ANamedVectorTypesNetHasItsBits) {
  Run("module top;\n"
      "  typedef logic [3:0] t;\n"
      "  nettype logic [7:4] n4;\n"
      "  wire t x;\n"
      "  n4 n;\n"
      "endmodule\n");
  auto names_of_bits = [](vpiHandle net) {
    std::vector<std::string> names;
    vpiHandle it = vpi_iterate(vpiBit, net);
    if (it == nullptr) return names;
    while (vpiHandle bit = vpi_scan(it))
      names.emplace_back(vpi_get_str(vpiName, bit));
    return names;
  };
  EXPECT_EQ(names_of_bits(By("top.x")),
            (std::vector<std::string>{"x[3]", "x[2]", "x[1]", "x[0]"}));
  EXPECT_EQ(names_of_bits(By("top.n")),
            (std::vector<std::string>{"n[7]", "n[6]", "n[5]", "n[4]"}));
  vpiHandle bits = vpi_iterate(vpiBit, By("top.n"));
  ASSERT_NE(bits, nullptr);
  vpiHandle bit = vpi_scan(bits);
  ASSERT_NE(bit, nullptr);
  EXPECT_EQ(vpi_get(vpiNetType, bit), vpiNettypeNetSelect);
  EXPECT_EQ(vpi_iterate(vpiDriver, bit), nullptr);
}

TEST_F(NetKindsOfARun, ALogicTypedNetIsALogicNet) {
  Run(kNetDataTypes);
  EXPECT_EQ(KindOf("top.w"), vpiNet);
  EXPECT_EQ(KindOf("top.l"), vpiNet);
}

TEST_F(NetKindsOfARun, IntegerAndTimeNetsAreTheirOwnKinds) {
  Run(kNetDataTypes);
  EXPECT_EQ(KindOf("top.i"), vpiIntegerNet);
  EXPECT_EQ(KindOf("top.t"), vpiTimeNet);
}

TEST_F(NetKindsOfARun, AnEnumTypedNetIsAnEnumNet) {
  Run(kNetDataTypes);
  EXPECT_EQ(KindOf("top.e"), vpiEnumNet);
  EXPECT_EQ(KindOf("top.f"), vpiEnumNet);
}

TEST_F(NetKindsOfARun, APackedStructNetWithADimensionIsAPackedArrayNet) {
  Run(kNetDataTypes);
  EXPECT_EQ(KindOf("top.p"), vpiPackedArrayNet);
}

TEST_F(NetKindsOfARun, ANettypeNetIsTheKindOfItsDataType) {
  Run(kNetDataTypes);
  EXPECT_EQ(KindOf("top.n"), vpiIntNet);
  EXPECT_EQ(KindOf("top.b"), vpiBitNet);
}

TEST_F(NetKindsOfARun, AnArrayNetsNetsAreTheKindOfItsElementType) {
  Run("module top; wire integer n [0:1]; endmodule\n");
  vpiHandle array = By("top.n");
  EXPECT_EQ(vpi_get(vpiType, array), vpiNetArray);
  EXPECT_EQ(KindsOf(vpiIntegerNet, array),
            (std::vector<int>{vpiIntegerNet, vpiIntegerNet}));
}

TEST(NetKindModel, EachDataTypeMakesItsKindOfNet) {
  const std::vector<std::pair<DataTypeKind, int>> kKinds = {
      {DataTypeKind::kImplicit, vpiNet},
      {DataTypeKind::kLogic, vpiNet},
      {DataTypeKind::kStruct, vpiStructNet},
      {DataTypeKind::kUnion, vpiUnionNet},
      {DataTypeKind::kEnum, vpiEnumNet},
      {DataTypeKind::kInteger, vpiIntegerNet},
      {DataTypeKind::kTime, vpiTimeNet},
      {DataTypeKind::kBit, vpiBitNet},
      {DataTypeKind::kByte, vpiByteNet},
      {DataTypeKind::kShortint, vpiShortIntNet},
      {DataTypeKind::kInt, vpiIntNet},
      {DataTypeKind::kLongint, vpiLongIntNet},
      {DataTypeKind::kReal, vpiRealNet},
      {DataTypeKind::kRealtime, vpiRealNet},
      {DataTypeKind::kShortreal, vpiShortRealNet}};
  for (const auto& [data_kind, kind] : kKinds) {
    RtlirNet net;
    net.data_kind = data_kind;
    EXPECT_EQ(VpiNetObjectKind(net), kind) << static_cast<int>(data_kind);
  }
  RtlirNet interconnect;
  interconnect.net_type = NetType::kInterconnect;
  EXPECT_EQ(VpiNetObjectKind(interconnect), vpiInterconnectNet);
  for (DataTypeKind data_kind :
       {DataTypeKind::kStruct, DataTypeKind::kUnion, DataTypeKind::kEnum}) {
    RtlirNet net;
    net.data_kind = data_kind;
    net.has_declared_packed_dim = true;
    EXPECT_EQ(VpiNetObjectKind(net), vpiPackedArrayNet)
        << static_cast<int>(data_kind);
  }
}

class NetPortsOfARun : public VpiDesignRun {
 protected:
  static vpiHandle OnlyOf(int type, vpiHandle ref) {
    vpiHandle it = vpi_iterate(type, ref);
    if (it == nullptr) return nullptr;
    vpiHandle first = vpi_scan(it);
    return vpi_scan(it) == nullptr ? first : nullptr;
  }

  static vpiHandle BitOf(const char* name, int index) {
    return vpi_handle_by_index(By(name), index);
  }
};

constexpr const char* kNetPorts =
    "module sub(input wire [3:0] a, input wire s, input wire [1:0] c,\n"
    "           input wire [1:0] d, input wire [1:0] e, input wire n,\n"
    "           input wire [1:0] g, input wire h [0:1], input wire s2);\n"
    "endmodule\n"
    "module leaf(input wire z); endmodule\n"
    "module top;\n"
    "  wire [3:0] w; wire v; wire [1:0] p; wire q;\n"
    "  wire [1:0] x, y, m, k; wire [3:0] r; wire arr [0:1]; wire t, t2;\n"
    "  wire [3:0] w3;\n"
    "  sub u(.a(w), .s(v), .c({p[0], q}), .d({x, y}), .e(m & k), .n(),\n"
    "        .g(r[2:1]), .h(arr), .s2(w3[2]));\n"
    "  if (1) begin : gb leaf l(.z(t)); end\n"
    "  for (genvar i = 0; i < 1; i++) begin : ga leaf l(.z(t2)); end\n"
    "endmodule\n";

TEST_F(NetPortsOfARun, AWholeNetReachesItsPort) {
  Run(kNetPorts);
  EXPECT_EQ(NamesOf(vpiPorts, By("top.u.a")), std::vector<std::string>{"a"});
}

TEST_F(NetPortsOfARun, ANetBitReachesItsPortBit) {
  Run(kNetPorts);
  vpiHandle bit = BitOf("top.u.a", 2);
  vpiHandle port_bit = OnlyOf(vpiPorts, bit);
  ASSERT_NE(port_bit, nullptr);
  EXPECT_EQ(vpi_get(vpiType, port_bit), vpiPortBit);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLowConn, port_bit)), VpiObjectOf(bit));
}

TEST_F(NetPortsOfARun, AWholeOrScalarNetReachesTheInstancePort) {
  Run(kNetPorts);
  EXPECT_EQ(NamesOf(vpiPortInst, By("top.w")), std::vector<std::string>{"a"});
  EXPECT_EQ(KindsOf(vpiPortInst, By("top.v")), std::vector<int>{vpiPort});
  EXPECT_EQ(NamesOf(vpiPortInst, By("top.v")), std::vector<std::string>{"s"});
}

TEST_F(NetPortsOfARun, ANetBitReachesThePortBitItConnects) {
  Run(kNetPorts);
  vpiHandle port_bit = OnlyOf(vpiPortInst, BitOf("top.w", 1));
  ASSERT_NE(port_bit, nullptr);
  EXPECT_EQ(vpi_get(vpiType, port_bit), vpiPortBit);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLowConn, port_bit)),
            VpiObjectOf(BitOf("top.u.a", 1)));
}

TEST_F(NetPortsOfARun, AConcatenationPlacesEachNet) {
  Run(kNetPorts);
  vpiHandle port_bit = OnlyOf(vpiPortInst, By("top.q"));
  ASSERT_NE(port_bit, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLowConn, port_bit)),
            VpiObjectOf(BitOf("top.u.c", 0)));
  EXPECT_EQ(NamesOf(vpiPortInst, By("top.p")), std::vector<std::string>{"c"});
}

TEST_F(NetPortsOfARun, ANetBeyondThePortReachesNoPort) {
  Run(kNetPorts);
  EXPECT_TRUE(NamesOf(vpiPortInst, By("top.x")).empty());
  EXPECT_EQ(NamesOf(vpiPortInst, By("top.y")), std::vector<std::string>{"d"});
}

TEST_F(NetPortsOfARun, AnUntoldPlaceReachesTheWholePort) {
  Run(kNetPorts);
  EXPECT_EQ(KindsOf(vpiPortInst, BitOf("top.m", 0)), std::vector<int>{vpiPort});
}

constexpr const char* kPortNets =
    "typedef struct packed { logic a; logic b; } s_t;\n"
    "module sub(input wire [3:0] a, input wire integer i,\n"
    "           input wire enum logic [1:0] {A, B} e, input wire s_t [1:0] p,\n"
    "           output logic o);\n"
    "endmodule\n"
    "module body(b); input [1:0] b; wire [1:0] b; endmodule\n"
    "module top;\n"
    "  wire [3:0] w; wire integer j; wire [3:0] q; logic r;\n"
    "  wire [1:0] c;\n"
    "  sub u(.a(w), .i(j), .e(), .p(q), .o(r)); body v(.b(c));\n"
    "endmodule\n";

TEST_F(NetKindsOfARun, AnAnsiPortsNetHasItsBits) {
  Run(kPortNets);
  EXPECT_EQ(KindsOf(vpiBit, By("top.u.a")), std::vector<int>(4, vpiNetBit));
}

TEST_F(NetKindsOfARun, ANonAnsiPortsBodyNetHasItsBits) {
  Run(kPortNets);
  EXPECT_EQ(KindOf("top.v.b"), vpiNet);
  EXPECT_EQ(KindsOf(vpiBit, By("top.v.b")), std::vector<int>(2, vpiNetBit));
}

TEST_F(NetKindsOfARun, AnAnsiPortsNetIsTheKindOfItsDataType) {
  Run(kPortNets);
  EXPECT_EQ(KindOf("top.u.a"), vpiNet);
  EXPECT_EQ(KindOf("top.u.i"), vpiIntegerNet);
  EXPECT_EQ(KindOf("top.u.e"), vpiEnumNet);
  EXPECT_EQ(KindOf("top.u.p"), vpiPackedArrayNet);
}

TEST_F(NetPortsOfARun, ASelectedOrArrayNetReachesTheWholePort) {
  Run(kNetPorts);
  EXPECT_EQ(NamesOf(vpiPortInst, By("top.r")), std::vector<std::string>{"g"});
  EXPECT_EQ(NamesOf(vpiPortInst, By("top.arr")), std::vector<std::string>{"h"});
}

TEST_F(NetPortsOfARun, AnInstanceInAGenerateBlockIsReached) {
  Run(kNetPorts);
  EXPECT_EQ(NamesOf(vpiPortInst, By("top.t")), std::vector<std::string>{"z"});
  EXPECT_EQ(NamesOf(vpiPortInst, By("top.t2")), std::vector<std::string>{"z"});
}

TEST(NetPortModel, ANetNoInstanceHoldsReachesNoPort) {
  VpiObject net;
  net.type = vpiNet;
  VpiObject bit;
  bit.type = vpiNetBit;
  VpiObject orphan_bit;
  orphan_bit.type = vpiNetBit;
  bit.parent = &net;
  VpiObject scope;
  scope.type = vpiGenScope;
  VpiObject scoped;
  scoped.type = vpiNet;
  scoped.parent = &scope;
  for (VpiObject* ref : {&net, &bit, &orphan_bit, &scoped}) {
    EXPECT_TRUE(VpiNetPorts(ref).empty());
    EXPECT_TRUE(VpiNetPortInsts(ref).empty());
  }
}

TEST_F(NetPortsOfARun, ABitBelowASelectReachesNoPort) {
  Run(kNetPorts);
  EXPECT_TRUE(NamesOf(vpiPortInst, BitOf("top.w3", 0)).empty());
  EXPECT_EQ(NamesOf(vpiPortInst, BitOf("top.w3", 2)),
            std::vector<std::string>{"s2"});
  EXPECT_EQ(NamesOf(vpiPortInst, By("top.w3")), std::vector<std::string>{"s2"});
}

TEST_F(NetPortsOfARun, ABitReachesItsPlaceWhateverOrderItsVectorStandsIn) {
  Run("module sub(input wire [1:0] a); endmodule\n"
      "module top; wire [1:0] y; sub u(.a({y[0], y[1]})); endmodule\n");
  vpiHandle high = OnlyOf(vpiPortInst, BitOf("top.y", 0));
  ASSERT_NE(high, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLowConn, high)),
            VpiObjectOf(BitOf("top.u.a", 1)));
  vpiHandle low = OnlyOf(vpiPortInst, BitOf("top.y", 1));
  ASSERT_NE(low, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLowConn, low)),
            VpiObjectOf(BitOf("top.u.a", 0)));
}

TEST(NetKindModel, AModulesNetsAreItsBodysAndItsNetPorts) {
  RtlirModule mod;
  RtlirNet body;
  body.name = "a";
  mod.nets.push_back(body);
  DataType aggregate;
  aggregate.kind = DataTypeKind::kStruct;
  const std::vector<std::pair<std::string_view, NetType>> kPorts = {
      {"a", NetType::kWire},
      {"p", NetType::kWire},
      {"v", NetType::kNone},
      {"ic", NetType::kInterconnect}};
  for (const auto& [name, net_type] : kPorts) {
    RtlirPort& port = mod.ports.emplace_back();
    port.name = name;
    port.net_type = net_type;
    port.is_interconnect = net_type == NetType::kInterconnect;
  }
  mod.ports[1].dtype = &aggregate;
  mod.ports[1].data_kind = DataTypeKind::kStruct;
  const std::vector<RtlirNet> kNets = VpiDeclaredNets(mod);
  ASSERT_EQ(kNets.size(), 2u);
  EXPECT_EQ(kNets[0].name, "a");
  EXPECT_EQ(kNets[1].name, "p");
  EXPECT_FALSE(kNets[1].has_declared_packed_dim);
  EXPECT_EQ(VpiNetObjectKind(kNets[1]), vpiStructNet);
}

TEST(NetKindModel, AMultidimensionalNetArrayHasNoNetKeys) {
  RtlirNet net;
  net.name = "n";
  net.num_unpacked_dims = 2;
  net.unpacked_dims = {{0, 1}, {0, 2}};
  EXPECT_TRUE(VpiDeclaredNetKeys(net, "top").empty());
}

TEST_F(ArrayNetsOfARun, ANetArrayBelowZeroIsAnArrayNet) {
  Run("module top; wire n [-1:0]; endmodule\n");
  EXPECT_EQ(vpi_get(vpiType, Array()), vpiNetArray);
  EXPECT_TRUE(NamesOf(vpiNet, Array()).empty());
}

TEST(NetKindModel, TheNetClassGroupsTheConcreteNetKinds) {
  for (int kind : {vpiNet, vpiStructNet, vpiUnionNet, vpiEnumNet, vpiIntegerNet,
                   vpiTimeNet, vpiBitNet, vpiByteNet, vpiShortIntNet, vpiIntNet,
                   vpiLongIntNet, vpiRealNet, vpiShortRealNet,
                   vpiPackedArrayNet, vpiInterconnectNet}) {
    EXPECT_TRUE(VpiIsNetClassType(kind)) << kind;
  }
  for (int kind : {vpiNetBit, vpiNetArray, vpiInterconnectArray, vpiReg}) {
    EXPECT_FALSE(VpiIsNetClassType(kind)) << kind;
  }
}

TEST_F(ArrayNetsOfARun, AnInstancesNetIterationReachesEveryNetKind) {
  Run("module top; typedef enum logic [1:0] {A, B} e_t;\n"
      "  typedef struct packed { logic x; } s_t;\n"
      "  wire l; wire integer i; wire e_t e; wire s_t s; wire n [1:0];\n"
      "endmodule\n");
  EXPECT_EQ(NamesOf(vpiNet, By("top")),
            (std::vector<std::string>{"e", "i", "l", "s"}));
  EXPECT_EQ(vpi_get(vpiType, Named(vpiNet, By("top"), "e")), vpiEnumNet);
  EXPECT_EQ(vpi_get(vpiType, Named(vpiNet, By("top"), "i")), vpiIntegerNet);
  EXPECT_EQ(vpi_get(vpiType, Named(vpiNet, By("top"), "s")), vpiStructNet);
}

class NetRelationsOfARun : public VpiDesignRun {
 protected:
  static int CountOf(int type, vpiHandle ref, int kind) {
    const std::vector<int> kKinds = KindsOf(type, ref);
    return static_cast<int>(std::ranges::count(kKinds, kind));
  }

  static vpiHandle BitOf(const char* name, int index) {
    return vpi_handle_by_index(By(name), index);
  }

  static constexpr const char* kPortDesign =
      "module sub(input c, output d, output logic v, inout io);\n"
      "  assign d = c;\n"
      "  always_comb v = c;\n"
      "endmodule\n"
      "module pair(input a2, input b2, output o2);\n"
      "  assign o2 = a2 & b2;\n"
      "endmodule\n"
      "module top; wire x, y, z, e, g; wire [1:0] b;\n"
      "  logic k; logic [1:0] kv;\n"
      "  sub u(.c(k), .d(z), .v(y), .io());\n"
      "  sub w(.c(x), .d(), .v(), .io());\n"
      "  sub n(.c(), .d(), .v(), .io());\n"
      "  sub s(.c(b[1:1]), .d(), .v(), .io());\n"
      "  sub p(.c(kv[1:1]), .d(), .v(), .io());\n"
      "  sub q(.c({e}), .d(), .v(), .io());\n"
      "  sub t(.c(1'b1), .d(), .v(), .io());\n"
      "  sub r(.c(x & e), .d(), .v(), .io());\n"
      "  sub m(.c({k}), .d(), .v(), .io());\n"
      "  sub h(.c(b[0]), .d(), .v(), .io());\n"
      "  pair pr(.a2(g), .b2(g), .o2());\n"
      "endmodule\n";
};

TEST_F(NetRelationsOfARun, AnAssignmentIsReachedFromAScalarOrABitAlone) {
  Run("module top; wire [3:0] w; wire s; wire [1:0] t;\n"
      "  assign w = 4'h1;\n"
      "  assign s = w[2];\n"
      "  assign t = w[3:2];\n"
      "endmodule\n");
  vpiHandle w = By("top.w");
  ASSERT_NE(w, nullptr);
  EXPECT_TRUE(KindsOf(vpiContAssign, w).empty());
  EXPECT_EQ(KindsOf(vpiContAssign, vpi_handle_by_index(w, 1)).size(), 1u);
  EXPECT_EQ(KindsOf(vpiContAssign, vpi_handle_by_index(w, 2)).size(), 3u);
  EXPECT_EQ(KindsOf(vpiContAssign, vpi_handle_by_index(w, 3)).size(), 2u);
  EXPECT_EQ(KindsOf(vpiContAssign, By("top.s")),
            std::vector<int>{vpiContAssign});
}

TEST(NetContAssignModel, ABitNoVectorHoldsReachesNoAssignment) {
  VpiObject bit;
  bit.type = vpiNetBit;
  EXPECT_TRUE(VpiNetContAssigns(&bit).empty());
}

TEST_F(NetRelationsOfARun, ADriverIterationReachesAPortAVariableDrives) {
  Run(kPortDesign);
  EXPECT_EQ(CountOf(vpiDriver, By("top.y"), vpiPort), 1);
  EXPECT_EQ(CountOf(vpiDriver, By("top.z"), vpiPort), 0);
  EXPECT_EQ(CountOf(vpiDriver, By("top.u.c"), vpiPort), 1);
  EXPECT_EQ(CountOf(vpiDriver, By("top.w.c"), vpiPort), 0);
  EXPECT_EQ(CountOf(vpiDriver, By("top.u.d"), vpiPort), 0);
  EXPECT_EQ(CountOf(vpiDriver, By("top.n.c"), vpiPort), 0);
  EXPECT_EQ(CountOf(vpiDriver, By("top.s.c"), vpiPort), 0);
  EXPECT_EQ(CountOf(vpiDriver, By("top.q.c"), vpiPort), 0);
  EXPECT_EQ(CountOf(vpiDriver, By("top.p.c"), vpiPort), 1);
  EXPECT_EQ(CountOf(vpiDriver, By("top.t.c"), vpiPort), 1);
  EXPECT_EQ(CountOf(vpiDriver, By("top.r.c"), vpiPort), 1);
  EXPECT_EQ(CountOf(vpiDriver, By("top.m.c"), vpiPort), 1);
  EXPECT_EQ(CountOf(vpiDriver, By("top.h.c"), vpiPort), 0);
}

TEST_F(NetRelationsOfARun, LocalDriversAndLoadsTakeInTheInstancesOwnPorts) {
  Run(kPortDesign);
  EXPECT_EQ(CountOf(vpiLocalDriver, By("top.w.c"), vpiPort), 1);
  EXPECT_EQ(CountOf(vpiLocalLoad, By("top.w.c"), vpiPort), 0);
  EXPECT_EQ(CountOf(vpiLocalLoad, By("top.w.c"), vpiContAssign), 1);
  EXPECT_EQ(CountOf(vpiLocalDriver, By("top.w.c"), vpiContAssign), 0);
  EXPECT_EQ(CountOf(vpiLocalLoad, By("top.w.d"), vpiPort), 1);
  EXPECT_EQ(CountOf(vpiLocalDriver, By("top.w.d"), vpiPort), 0);
  EXPECT_EQ(CountOf(vpiLocalDriver, By("top.w.d"), vpiContAssign), 1);
  EXPECT_EQ(CountOf(vpiLocalDriver, By("top.w.io"), vpiPort), 1);
  EXPECT_EQ(CountOf(vpiLocalLoad, By("top.w.io"), vpiPort), 1);
}

TEST_F(NetRelationsOfARun, DriversAndLoadsReachAcrossAPortNetsDrive) {
  Run(kPortDesign);
  EXPECT_EQ(CountOf(vpiDriver, By("top.z"), vpiContAssign), 1);
  EXPECT_EQ(CountOf(vpiLocalDriver, By("top.z"), vpiContAssign), 0);
  EXPECT_EQ(CountOf(vpiLoad, By("top.x"), vpiContAssign), 1);
  EXPECT_EQ(CountOf(vpiLocalLoad, By("top.x"), vpiContAssign), 0);
  EXPECT_EQ(CountOf(vpiLoad, By("top.e"), vpiContAssign), 1);
  EXPECT_EQ(CountOf(vpiLoad, By("top.g"), vpiContAssign), 1);
}

TEST_F(NetRelationsOfARun, ABitsDriversAndLoadsFollowItAcrossAPort) {
  Run("module sub(output [1:0] d, input [1:0] a);\n"
      "  assign d[0] = a[1];\n"
      "  initial force d[1] = 1'b0;\n"
      "endmodule\n"
      "module top; wire [1:0] z, y, v, y2; wire s; logic k; integer i;\n"
      "  assign v = 2'b10;\n"
      "  sub u(.d(z), .a({y[0], y[1]}));\n"
      "  sub w(.d(v[1]), .a({y[0]}));\n"
      "  sub o(.d(), .a(y & v));\n"
      "  sub g(.d({s, y2[1]}), .a({y2[i], y2[0]}));\n"
      "  sub e(.d(), .a({k, y2[1]}));\n"
      "endmodule\n");
  EXPECT_EQ(CountOf(vpiDriver, BitOf("top.z", 0), vpiContAssign), 1);
  EXPECT_EQ(CountOf(vpiDriver, BitOf("top.z", 0), vpiForce), 0);
  EXPECT_EQ(CountOf(vpiDriver, BitOf("top.z", 1), vpiContAssign), 0);
  EXPECT_EQ(CountOf(vpiDriver, BitOf("top.z", 1), vpiForce), 1);
  EXPECT_EQ(CountOf(vpiLoad, BitOf("top.y", 0), vpiContAssign), 1);
  EXPECT_EQ(CountOf(vpiLoad, BitOf("top.y", 1), vpiContAssign), 0);
  EXPECT_EQ(CountOf(vpiDriver, BitOf("top.v", 0), vpiContAssign), 1);
  EXPECT_EQ(CountOf(vpiDriver, BitOf("top.v", 1), vpiContAssign), 2);
  EXPECT_EQ(CountOf(vpiDriver, BitOf("top.o.d", 0), vpiContAssign), 1);
  EXPECT_EQ(CountOf(vpiDriver, BitOf("top.y2", 1), vpiContAssign), 1);
  EXPECT_EQ(CountOf(vpiDriver, BitOf("top.y2", 0), vpiContAssign), 0);
  EXPECT_EQ(CountOf(vpiLocalDriver, BitOf("top.u.d", 0), vpiContAssign), 1);
  EXPECT_EQ(CountOf(vpiLocalDriver, BitOf("top.z", 0), vpiContAssign), 0);
}

TEST_F(NetRelationsOfARun, ABitsDriversAndLoadsTakeThePrimTermsOnIt) {
  Run("module sub(input [1:0] a); wire w; and h(w, a[1], a[0]); endmodule\n"
      "module top; wire [1:0] z; wire a, b, y;\n"
      "  and g(z[0], a, b);\n"
      "  buf f(y, z[1]);\n"
      "  sub u(.a(z));\n"
      "endmodule\n");
  EXPECT_EQ(CountOf(vpiDriver, BitOf("top.z", 0), vpiPrimTerm), 1);
  EXPECT_EQ(CountOf(vpiDriver, BitOf("top.z", 1), vpiPrimTerm), 0);
  EXPECT_EQ(CountOf(vpiLoad, BitOf("top.z", 0), vpiPrimTerm), 1);
  EXPECT_EQ(CountOf(vpiLoad, BitOf("top.z", 1), vpiPrimTerm), 2);
  EXPECT_EQ(CountOf(vpiLocalLoad, BitOf("top.z", 1), vpiPrimTerm), 1);
}

TEST_F(NetRelationsOfARun, ABitsDriversTakeThePortBitsANonNetDrives) {
  Run("module sub(input [1:0] a, input [1:0] b, input [1:0] c,\n"
      "           input [1:0] d, input [1:0] e);\n"
      "endmodule\n"
      "module top; logic [1:0] k; wire [1:0] n; logic m;\n"
      "  sub u(.a(k), .b({m, n[0]}), .c(n & k), .d({m}), .e());\n"
      "endmodule\n");
  EXPECT_EQ(CountOf(vpiDriver, BitOf("top.u.a", 0), vpiPortBit), 1);
  EXPECT_EQ(CountOf(vpiDriver, BitOf("top.u.b", 1), vpiPortBit), 1);
  EXPECT_EQ(CountOf(vpiDriver, BitOf("top.u.b", 0), vpiPortBit), 0);
  EXPECT_EQ(CountOf(vpiDriver, BitOf("top.u.c", 0), vpiPortBit), 1);
  EXPECT_EQ(CountOf(vpiDriver, BitOf("top.u.d", 0), vpiPortBit), 1);
  EXPECT_EQ(CountOf(vpiDriver, BitOf("top.u.d", 1), vpiPortBit), 0);
  EXPECT_EQ(CountOf(vpiDriver, BitOf("top.u.e", 0), vpiPortBit), 0);
}

TEST_F(NetKindsOfARun, ANetReachesTheTypespecOfItsType) {
  Run(kNetDataTypes);
  vpiHandle named = vpi_handle(vpiTypespec, By("top.e"));
  ASSERT_NE(named, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, named), "e_t");
  EXPECT_EQ(TypespecKindOf("top.w"), vpiLogicTypespec);
  EXPECT_EQ(TypespecKindOf("top.l"), vpiLogicTypespec);
  EXPECT_EQ(TypespecKindOf("top.i"), vpiIntegerTypespec);
  EXPECT_EQ(TypespecKindOf("top.t"), vpiTimeTypespec);
}

TEST_F(NetKindsOfARun, AnArrayOrPortNetReachesTheTypespecOfItsType) {
  Run("typedef logic [7:0] byte_t;\n"
      "module sub(input byte_t a, input wire [2:0] b); endmodule\n"
      "module body(c); input byte_t c; endmodule\n"
      "module top; wire integer n [0:1]; sub u(); body v(); endmodule\n");
  EXPECT_EQ(TypespecKindOf("top.n"), vpiArrayTypespec);
  vpiHandle a = vpi_handle(vpiTypespec, By("top.u.a"));
  ASSERT_NE(a, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, a), "byte_t");
  EXPECT_EQ(TypespecKindOf("top.u.b"), vpiLogicTypespec);
  vpiHandle c = vpi_handle(vpiTypespec, By("top.v.c"));
  ASSERT_NE(c, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, c), "byte_t");
}

TEST_F(NetKindsOfARun, AnInterconnectsNetTypeIsInterconnect) {
  Run("module leaf(interconnect p, interconnect q [0:1]); endmodule\n"
      "module sink(inout wor r); endmodule\n"
      "module top; interconnect c; leaf u(); sink v(c); endmodule\n");
  for (const char* name : {"p", "q"}) {
    vpiHandle port = Named(vpiPort, By("top.u"), name);
    ASSERT_NE(port, nullptr);
    vpiHandle net = vpi_handle(vpiLowConn, port);
    ASSERT_NE(net, nullptr);
    EXPECT_EQ(vpi_get(vpiNetType, net), vpiInterconnect) << name;
    EXPECT_STREQ(vpi_get_str(vpiNetType, net), "vpiInterconnect") << name;
  }
  EXPECT_EQ(vpi_get(vpiNetType, By("top.c")), vpiInterconnect);
  EXPECT_EQ(vpi_get(vpiResolvedNetType, By("top.c")), vpiWor);
}

}  // namespace
}  // namespace delta
