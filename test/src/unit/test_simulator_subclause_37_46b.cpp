#include <gtest/gtest.h>

#include <algorithm>
#include <fstream>
#include <ios>
#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class DriversAndLoadsOfEveryNet : public VpiDesignRun {
 protected:
  static bool Holds(const std::vector<int>& kinds, int kind) {
    return std::ranges::find(kinds, kind) != kinds.end();
  }

  static std::vector<int> LinesOf(int relation, vpiHandle net, int kind) {
    std::vector<int> lines;
    for (vpiHandle obj : ObjectsOf(relation, net)) {
      if (vpi_get(vpiType, obj) == kind) {
        lines.push_back(vpi_get(vpiLineNo, obj));
      }
    }
    return lines;
  }

  static vpiHandle FirstOfKind(int relation, vpiHandle net, int kind) {
    for (vpiHandle obj : ObjectsOf(relation, net)) {
      if (vpi_get(vpiType, obj) == kind) return obj;
    }
    return nullptr;
  }
};

TEST_F(DriversAndLoadsOfEveryNet,
       DISABLED_AVectorAssignmentsBitDrivesTheNetBitItWrites) {
  Run("module top; wire [3:0] w, a;\n"
      "  assign w = a;\n"
      "endmodule\n");
  vpiHandle bit = FirstOfKind(vpiDriver, vpi_handle_by_index(By("top.w"), 2),
                              vpiContAssignBit);
  ASSERT_NE(bit, nullptr);
  EXPECT_EQ(vpi_get(vpiOffset, bit), 2);
}

TEST_F(DriversAndLoadsOfEveryNet,
       DISABLED_AVectorAssignmentsBitLoadsTheNetBitItReads) {
  Run("module top; wire [3:0] w, a;\n"
      "  assign w = a;\n"
      "endmodule\n");
  vpiHandle bit = FirstOfKind(vpiLoad, vpi_handle_by_index(By("top.a"), 2),
                              vpiContAssignBit);
  ASSERT_NE(bit, nullptr);
  EXPECT_EQ(vpi_get(vpiOffset, bit), 2);
}

struct NetKind {
  const char* name;
  const char* declarations;
};

class EveryKindOfNet : public DriversAndLoadsOfEveryNet,
                       public ::testing::WithParamInterface<NetKind> {
 protected:
  void RunAssignmentsAroundTheNet() {
    Run(std::string("module top;\n") + GetParam().declarations +
        "\n"
        "  assign n = src;\n"
        "  assign dst = n;\n"
        "endmodule\n");
  }
};

TEST_P(EveryKindOfNet, TheAssignmentWritingItIsItsOnlyDriver) {
  RunAssignmentsAroundTheNet();
  EXPECT_EQ(LinesOf(vpiDriver, By("top.n"), vpiContAssign),
            std::vector<int>{3});
}

TEST_P(EveryKindOfNet, TheAssignmentReadingItIsItsOnlyLoad) {
  RunAssignmentsAroundTheNet();
  EXPECT_EQ(LinesOf(vpiLoad, By("top.n"), vpiContAssign), std::vector<int>{4});
}

std::string NetKindName(const ::testing::TestParamInfo<NetKind>& info) {
  return info.param.name;
}

INSTANTIATE_TEST_SUITE_P(
    OfTheNetsClass, EveryKindOfNet,
    ::testing::Values(
        NetKind{"StructNet",
                "  typedef struct packed { logic a; logic b; } s_t; "
                "wire s_t n, src, dst;"},
        NetKind{
            "EnumNet",
            "  typedef enum logic [1:0] { A, B } e_t; wire e_t n, src, dst;"},
        NetKind{"IntegerNet", "  wire integer n, src, dst;"},
        NetKind{"TimeNet", "  wire time n, src, dst;"},
        NetKind{"ArrayNet", "  wire [1:0] n [2], src [2], dst [2];"}),
    NetKindName);

TEST_F(DriversAndLoadsOfEveryNet, AnArrayNetsElementAssignmentsDriveAndLoadIt) {
  Run("module top; wire [1:0] n [2]; wire [1:0] s, d;\n"
      "  assign n[0] = s;\n"
      "  assign d = n[1];\n"
      "endmodule\n");
  EXPECT_EQ(LinesOf(vpiDriver, By("top.n"), vpiContAssign),
            std::vector<int>{2});
  EXPECT_EQ(LinesOf(vpiLoad, By("top.n"), vpiContAssign), std::vector<int>{3});
}

TEST_F(DriversAndLoadsOfEveryNet,
       AnInterconnectArraysDriverIsThePortWritingIt) {
  Run("module drv(output logic o); assign o = 1'b1; endmodule\n"
      "module rcv(input logic i); endmodule\n"
      "module top; interconnect ic [2];\n"
      "  drv d(ic[0]);\n"
      "  rcv r(ic[0]);\n"
      "endmodule\n");
  EXPECT_TRUE(Holds(KindsOf(vpiDriver, By("top.ic")), vpiPort));
}

TEST_F(DriversAndLoadsOfEveryNet, AnInterconnectArraysLoadIsADelayTermOnIt) {
  const std::string kSdf = "/tmp/delta_c37_46_interconnect_array.sdf";
  std::ofstream(kSdf, std::ios::trunc)
      << "(DELAYFILE (CELL (CELLTYPE \"top\") (INSTANCE top) (DELAY "
         "(ABSOLUTE (PORT r/i (3))))))";
  Run("module drv(output logic o); assign o = 1'b1; endmodule\n"
      "module rcv(input logic i); endmodule\n"
      "module top; interconnect ic [2];\n"
      "  drv d(ic[0]);\n"
      "  rcv r(ic[0]);\n"
      "  initial $sdf_annotate(\"" +
      kSdf +
      "\");\n"
      "endmodule\n");
  EXPECT_TRUE(Holds(KindsOf(vpiLoad, By("top.ic")), vpiDelayTerm));
}

TEST_F(DriversAndLoadsOfEveryNet, AnInterfacesNetsReportTheAssignmentsInIt) {
  Run("interface ifc; wire a, y;\n"
      "  assign y = a;\n"
      "endinterface\n"
      "module top; ifc i(); endmodule\n");
  EXPECT_EQ(LinesOf(vpiDriver, By("top.i.y"), vpiContAssign),
            std::vector<int>{2});
  EXPECT_EQ(LinesOf(vpiLoad, By("top.i.a"), vpiContAssign),
            std::vector<int>{2});
}

struct PortConnection {
  const char* name;
  const char* receiver;
  const char* top_items;
  std::vector<const char*> nets;
  bool is_load;
};

class EveryInputPortConnection
    : public DriversAndLoadsOfEveryNet,
      public ::testing::WithParamInterface<PortConnection> {};

TEST_P(EveryInputPortConnection, ThePortIsALoadOnlyOfAComplexExpression) {
  Run(std::string(GetParam().receiver) + "module top;\n" +
      GetParam().top_items + "\nendmodule\n");
  for (const char* net : GetParam().nets) {
    SCOPED_TRACE(net);
    EXPECT_EQ(Holds(KindsOf(vpiLoad, By(net)), vpiPort), GetParam().is_load);
  }
}

std::string PortConnectionName(
    const ::testing::TestParamInfo<PortConnection>& info) {
  return info.param.name;
}

constexpr const char* kScalarRam = "module ram(input logic p); endmodule\n";
constexpr const char* kVectorRam =
    "module ram(input logic [1:0] p); endmodule\n";

INSTANTIATE_TEST_SUITE_P(
    OnAnInputPort, EveryInputPortConnection,
    ::testing::Values(
        PortConnection{"AConcatenation",
                       kVectorRam,
                       "  wire a, b; ram r({a, b});",
                       {"top.a", "top.b"},
                       false},
        PortConnection{"AReplication",
                       kVectorRam,
                       "  wire a; ram r({2{a}});",
                       {"top.a"},
                       false},
        PortConnection{"AnOperationOfTwoNets",
                       kScalarRam,
                       "  wire a, b; ram r(a & b);",
                       {"top.a", "top.b"},
                       true},
        PortConnection{"NestedOperations",
                       kScalarRam,
                       "  wire a, b, c; ram r(!(a | (b & c)));",
                       {"top.a", "top.b", "top.c"},
                       true},
        PortConnection{"AnOperationOnABitSelect",
                       kScalarRam,
                       "  wire [1:0] v; ram r(!v[1]);",
                       {"top.v"},
                       true},
        PortConnection{"AVectorOperation",
                       kVectorRam,
                       "  wire [1:0] v; ram r(~v);",
                       {"top.v"},
                       true},
        PortConnection{"ANamedConnection",
                       kScalarRam,
                       "  wire t; ram r(.p(!t));",
                       {"top.t"},
                       true},
        PortConnection{"AnInstanceInAGenerateBlock",
                       kScalarRam,
                       "  wire t; if (1) begin : g ram r(!t); end",
                       {"top.t"},
                       true},
        PortConnection{"AnInterfaceInstance",
                       "interface ifc(input logic p); endinterface\n",
                       "  wire t; ifc i(!t);",
                       {"top.t"},
                       true},
        PortConnection{"AProgramInstance",
                       "program prg(input logic p); endprogram\n",
                       "  wire t; prg g(!t);",
                       {"top.t"},
                       true}),
    PortConnectionName);

TEST_F(DriversAndLoadsOfEveryNet,
       DISABLED_AVectorPortsBitIsALoadOfTheNetBitItReads) {
  Run(std::string(kVectorRam) +
      "module top; wire [1:0] v; ram r(~v); endmodule\n");
  EXPECT_TRUE(
      Holds(KindsOf(vpiLoad, vpi_handle_by_index(By("top.v"), 1)), vpiPortBit));
}

TEST_F(DriversAndLoadsOfEveryNet,
       DISABLED_AnOperationOnAPartSelectMakesThePortALoad) {
  Run(std::string(kVectorRam) +
      "module top; wire [3:0] v; ram r(~v[1:0]); endmodule\n");
  EXPECT_TRUE(Holds(KindsOf(vpiLoad, By("top.v")), vpiPort));
}

TEST_F(DriversAndLoadsOfEveryNet, ALoadPortsHighConnIsTheComplexExpression) {
  Run(std::string(kScalarRam) +
      "module top; wire trinet; ram r0(!trinet); endmodule\n");
  vpiHandle port = FirstOfKind(vpiLoad, By("top.trinet"), vpiPort);
  ASSERT_NE(port, nullptr);
  vpiHandle expr = vpi_handle(vpiHighConn, port);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(vpi_get(vpiType, expr), vpiOperation);
  EXPECT_EQ(vpi_get(vpiOpType, expr), vpiNotOp);
}

}  // namespace
}  // namespace delta
