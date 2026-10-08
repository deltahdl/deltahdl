#include <gtest/gtest.h>

#include <string>
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

// A design run with a PLI application registered, its array nets read back
// once the run is over.
class ArrayNetsOfARun : public VpiDesignRun {
 protected:
  // The integer value of an object.
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

// §37.16 detail 1: a net declared with an unpacked dimension is an array net.
TEST_F(ArrayNetsOfARun, ANetWithAnUnpackedDimensionIsAnArrayNet) {
  Run(kArrayNet);
  EXPECT_EQ(vpi_get(vpiType, Array()), vpiNetArray);
}

// §37.16 detail 24: an array net's vpiSize is the number of nets it holds.
TEST_F(ArrayNetsOfARun, AnArrayNetsSizeIsTheNumberOfItsNets) {
  Run(kArrayNet);
  EXPECT_EQ(vpi_get(vpiSize, Array()), 3);
}

// §37.16 detail 2: each net of an array net is an array member, whose
// vpiParent is the array net.
TEST_F(ArrayNetsOfARun, EachNetOfAnArrayNetIsAnArrayMember) {
  Run(kArrayNet);
  vpiHandle element = vpi_handle_by_index(Array(), 1);
  ASSERT_NE(element, nullptr);
  EXPECT_EQ(vpi_get(vpiType, element), vpiNet);
  EXPECT_EQ(vpi_get(vpiArrayMember, element), 1);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, element)), VpiObjectOf(Array()));
}

// §37.16 (figure): a module reaches its array net through vpiNetArray and no
// longer meets the array's nets among its own, which the array net reaches.
TEST_F(ArrayNetsOfARun, TheArrayNetHoldsItsNetsInPlaceOfTheModule) {
  Run(kArrayNet);
  EXPECT_EQ(NamesOf(vpiNetArray, By("top")), std::vector<std::string>{"n"});
  EXPECT_TRUE(NamesOf(vpiNet, By("top")).empty());
  EXPECT_EQ(NamesOf(vpiNet, Array()),
            (std::vector<std::string>{"n[0]", "n[1]", "n[2]"}));
}

// §37.16 (figure): the net bits are the array's nets', each holding its bit of
// that net's value; the array net has none of its own.
TEST_F(ArrayNetsOfARun, TheBitsAreTheArrayNetsNets) {
  Run(kArrayNet);
  vpiHandle element = vpi_handle_by_index(Array(), 1);
  ASSERT_NE(element, nullptr);
  EXPECT_EQ(IntOf(element), 0b1010);
  EXPECT_EQ(IntOf(vpi_handle_by_index(element, 1)), 1);
  EXPECT_EQ(vpi_iterate(vpiBit, Array()), nullptr);
}

// A design run with a PLI application registered, its nets' object kinds read
// back once the run is over.
class NetKindsOfARun : public VpiDesignRun {
 protected:
  static int KindOf(const char* name) { return vpi_get(vpiType, By(name)); }
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

// §37.16 (figure): a net with no data type of its own, or of logic, is a logic
// net.
TEST_F(NetKindsOfARun, ALogicTypedNetIsALogicNet) {
  Run(kNetDataTypes);
  EXPECT_EQ(KindOf("top.w"), vpiNet);
  EXPECT_EQ(KindOf("top.l"), vpiNet);
}

// §37.16 (figure): an integer net and a time net are the kinds of their types.
TEST_F(NetKindsOfARun, IntegerAndTimeNetsAreTheirOwnKinds) {
  Run(kNetDataTypes);
  EXPECT_EQ(KindOf("top.i"), vpiIntegerNet);
  EXPECT_EQ(KindOf("top.t"), vpiTimeNet);
}

// §37.16 (figure): a net of an enum type, named or written in place, is an enum
// net.
TEST_F(NetKindsOfARun, AnEnumTypedNetIsAnEnumNet) {
  Run(kNetDataTypes);
  EXPECT_EQ(KindOf("top.e"), vpiEnumNet);
  EXPECT_EQ(KindOf("top.f"), vpiEnumNet);
}

// §37.16 detail 1: a packed struct net with a packed dimension of its own is a
// packed array net.
TEST_F(NetKindsOfARun, APackedStructNetWithADimensionIsAPackedArrayNet) {
  Run(kNetDataTypes);
  EXPECT_EQ(KindOf("top.p"), vpiPackedArrayNet);
}

// §37.16 (figure) with §6.6.7: a net of a user-defined nettype is the kind of
// the nettype's data type, a 2-state one among them.
TEST_F(NetKindsOfARun, ANettypeNetIsTheKindOfItsDataType) {
  Run(kNetDataTypes);
  EXPECT_EQ(KindOf("top.n"), vpiIntNet);
  EXPECT_EQ(KindOf("top.b"), vpiBitNet);
}

// §37.16 (figure): each net of an array net is the kind of the array's element
// type.
TEST_F(NetKindsOfARun, AnArrayNetsNetsAreTheKindOfItsElementType) {
  Run("module top; wire integer n [0:1]; endmodule\n");
  vpiHandle array = By("top.n");
  EXPECT_EQ(vpi_get(vpiType, array), vpiNetArray);
  EXPECT_EQ(KindsOf(vpiIntegerNet, array),
            (std::vector<int>{vpiIntegerNet, vpiIntegerNet}));
}

// §37.16 (figure) and detail 1: the kind of net each data type makes, a
// dimension of its own turning a struct, union or enum net into a packed array
// net, and a logic net for a type the figure draws no box of its own for;
// §37.24: a generic interconnect is an interconnect net.
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

// A design run with a PLI application registered, the ports its nets reach
// read back once the run is over.
class NetPortsOfARun : public VpiDesignRun {
 protected:
  // The one object `ref` reaches through `type`, null unless there is exactly
  // one.
  static vpiHandle OnlyOf(int type, vpiHandle ref) {
    vpiHandle it = vpi_iterate(type, ref);
    if (it == nullptr) return nullptr;
    vpiHandle first = vpi_scan(it);
    return vpi_scan(it) == nullptr ? first : nullptr;
  }

  // The bit of the net `name` at `index`.
  static vpiHandle BitOf(const char* name, int index) {
    return vpi_handle_by_index(By(name), index);
  }
};

constexpr const char* kNetPorts =
    "module sub(input wire [3:0] a, input wire s, input wire [1:0] c,\n"
    "           input wire [1:0] d, input wire [1:0] e, input wire n,\n"
    "           input wire [1:0] g, input wire h [0:1]);\n"
    "endmodule\n"
    "module leaf(input wire z); endmodule\n"
    "module top;\n"
    "  wire [3:0] w; wire v; wire [1:0] p; wire q;\n"
    "  wire [1:0] x, y, m, k; wire [3:0] r; wire arr [0:1]; wire t, t2;\n"
    "  sub u(.a(w), .s(v), .c({p[0], q}), .d({x, y}), .e(m & k), .n(),\n"
    "        .g(r[2:1]), .h(arr));\n"
    "  if (1) begin : gb leaf l(.z(t)); end\n"
    "  for (genvar i = 0; i < 1; i++) begin : ga leaf l(.z(t2)); end\n"
    "endmodule\n";

// §37.16 detail 6: a whole net reaches through vpiPorts the port of its
// instance whose lowConn it is.
TEST_F(NetPortsOfARun, AWholeNetReachesItsPort) {
  Run(kNetPorts);
  EXPECT_EQ(NamesOf(vpiPorts, By("top.u.a")), std::vector<std::string>{"a"});
}

// §37.16 detail 6: a net bit reaches the port bit whose lowConn it is.
TEST_F(NetPortsOfARun, ANetBitReachesItsPortBit) {
  Run(kNetPorts);
  vpiHandle bit = BitOf("top.u.a", 2);
  vpiHandle port_bit = OnlyOf(vpiPorts, bit);
  ASSERT_NE(port_bit, nullptr);
  EXPECT_EQ(vpi_get(vpiType, port_bit), vpiPortBit);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLowConn, port_bit)), VpiObjectOf(bit));
}

// §37.16 detail 7: a whole net reaches through vpiPortInst the whole port its
// net is the highConn of, and a scalar net the scalar port.
TEST_F(NetPortsOfARun, AWholeOrScalarNetReachesTheInstancePort) {
  Run(kNetPorts);
  EXPECT_EQ(NamesOf(vpiPortInst, By("top.w")), std::vector<std::string>{"a"});
  EXPECT_EQ(KindsOf(vpiPortInst, By("top.v")), std::vector<int>{vpiPort});
  EXPECT_EQ(NamesOf(vpiPortInst, By("top.v")), std::vector<std::string>{"s"});
}

// §37.16 detail 7: a net bit reaches the port bit it is connected to.
TEST_F(NetPortsOfARun, ANetBitReachesThePortBitItConnects) {
  Run(kNetPorts);
  vpiHandle port_bit = OnlyOf(vpiPortInst, BitOf("top.w", 1));
  ASSERT_NE(port_bit, nullptr);
  EXPECT_EQ(vpi_get(vpiType, port_bit), vpiPortBit);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLowConn, port_bit)),
            VpiObjectOf(BitOf("top.u.a", 1)));
}

// §37.16 detail 7: within a concatenation, a scalar net reaches the port bit
// its place lands on, and a net one bit of which the concatenation selects
// reaches the whole port.
TEST_F(NetPortsOfARun, AConcatenationPlacesEachNet) {
  Run(kNetPorts);
  vpiHandle port_bit = OnlyOf(vpiPortInst, By("top.q"));
  ASSERT_NE(port_bit, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLowConn, port_bit)),
            VpiObjectOf(BitOf("top.u.c", 0)));
  EXPECT_EQ(NamesOf(vpiPortInst, By("top.p")), std::vector<std::string>{"c"});
}

// §37.16 detail 8: a net the highConn holds but whose bits all fall beyond the
// port's is connected to none of them, so its iteration leaves the port out.
TEST_F(NetPortsOfARun, ANetBeyondThePortReachesNoPort) {
  Run(kNetPorts);
  EXPECT_TRUE(NamesOf(vpiPortInst, By("top.x")).empty());
  EXPECT_EQ(NamesOf(vpiPortInst, By("top.y")), std::vector<std::string>{"d"});
}

// §37.16 detail 7: a net bit held in a highConn whose bit index cannot be told
// reaches the whole port.
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
    "module body(b); input b; wire [1:0] b; endmodule\n"
    "module top;\n"
    "  wire [3:0] w; wire integer j; wire [3:0] q; logic r;\n"
    "  wire [1:0] c;\n"
    "  sub u(.a(w), .i(j), .e(), .p(q), .o(r)); body v(.b(c));\n"
    "endmodule\n";

// §37.16 (figure): the net an ANSI port declares has a net bit per bit, as a
// net its module's body declares has.
TEST_F(NetKindsOfARun, AnAnsiPortsNetHasItsBits) {
  Run(kPortNets);
  EXPECT_EQ(KindsOf(vpiBit, By("top.u.a")), std::vector<int>(4, vpiNetBit));
  EXPECT_EQ(KindsOf(vpiBit, By("top.v.b")), std::vector<int>(2, vpiNetBit));
}

// §37.16 (figure) and detail 1: the net an ANSI port declares is the kind its
// data type makes it.
TEST_F(NetKindsOfARun, AnAnsiPortsNetIsTheKindOfItsDataType) {
  Run(kPortNets);
  EXPECT_EQ(KindOf("top.u.a"), vpiNet);
  EXPECT_EQ(KindOf("top.u.i"), vpiIntegerNet);
  EXPECT_EQ(KindOf("top.u.e"), vpiEnumNet);
  EXPECT_EQ(KindOf("top.u.p"), vpiPackedArrayNet);
}

// §37.16 detail 7: a net a select of which the highConn holds, at a place the
// select leaves untold, reaches the whole port, as an array net does.
TEST_F(NetPortsOfARun, ASelectedOrArrayNetReachesTheWholePort) {
  Run(kNetPorts);
  EXPECT_EQ(NamesOf(vpiPortInst, By("top.r")), std::vector<std::string>{"g"});
  EXPECT_EQ(NamesOf(vpiPortInst, By("top.arr")), std::vector<std::string>{"h"});
}

// §37.16 detail 7: the instances a net's module holds in its generate blocks
// have ports it reaches as well.
TEST_F(NetPortsOfARun, AnInstanceInAGenerateBlockIsReached) {
  Run(kNetPorts);
  EXPECT_EQ(NamesOf(vpiPortInst, By("top.t")), std::vector<std::string>{"z"});
  EXPECT_EQ(NamesOf(vpiPortInst, By("top.t2")), std::vector<std::string>{"z"});
}

// §37.16 details 6 and 7: a net or net bit no instance holds reaches no port.
TEST(NetPortModel, ANetNoInstanceHoldsReachesNoPort) {
  VpiObject net;
  net.type = vpiNet;
  VpiObject bit;
  bit.type = vpiNetBit;
  VpiObject orphan_bit;
  orphan_bit.type = vpiNetBit;
  bit.parent = &net;
  for (VpiObject* ref : {&net, &bit, &orphan_bit}) {
    EXPECT_TRUE(VpiNetPorts(ref).empty());
    EXPECT_TRUE(VpiNetPortInsts(ref).empty());
  }
}

}  // namespace
}  // namespace delta
