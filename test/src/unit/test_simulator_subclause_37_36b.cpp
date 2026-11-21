#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

#include "fixture_vpi_run.h"
#include "helpers_sealed_design_run.h"
#include "preprocessor/protect_processing.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class UdpRulesOfARun : public VpiDesignRun {
 protected:
  static vpiHandle Defn(std::string_view name) {
    return Named(vpiUdpDefn, nullptr, name);
  }

  static std::vector<int> RowSizesOf(std::string_view name) {
    std::vector<int> sizes;
    for (vpiHandle row : ObjectsOf(vpiTableEntry, Defn(name))) {
      sizes.push_back(vpi_get(vpiSize, row));
    }
    return sizes;
  }
};

constexpr const char* kKinds =
    "primitive ansi_or(output o, input a, b, c);\n"
    "  table 1 ? ? : 1; ? 1 ? : 1; ? ? 1 : 1; 0 0 0 : 0; endtable\n"
    "endprimitive\n"
    "extern primitive proto_and(output o, input a, b);\n"
    "primitive proto_and(output o, input a, b);\n"
    "  table 0 1 : 0; 1 1 : 1; ? 0 : 0; endtable\n"
    "endprimitive\n"
    "primitive latch(q, en, d);\n"
    "  output reg q; input en, d;\n"
    "  table 1 0 : ? : 0; 1 1 : ? : 1; 0 ? : ? : -; endtable\n"
    "endprimitive\n"
    "primitive flop(q, clk, d);\n"
    "  output reg q; input clk, d;\n"
    "  initial q = 1'b0;\n"
    "  table\n"
    "    (01) 0 : ? : 0;\n"
    "    r 1 : ? : 1;\n"
    "    (?0) ? : ? : -;\n"
    "  endtable\n"
    "endprimitive\n"
    "primitive gated(q, clk, d, en);\n"
    "  output reg q; input clk, d, en;\n"
    "  table\n"
    "    (x1) 0 1 : 0 : 0;\n"
    "    f ? ? : ? : -;\n"
    "  endtable\n"
    "endprimitive\n"
    "primitive hold(q, d);\n"
    "  output reg q; input d;\n"
    "  table 0 : ? : 0; 1 : ? : 1; endtable\n"
    "endprimitive\n"
    "module top;\n"
    "  reg a, b, c, en; wire o1, o2, q1, q2, q3, q4;\n"
    "  ansi_or u1(o1, a, b, c);\n"
    "  proto_and u2(o2, a, b);\n"
    "  latch u3(q1, en, a);\n"
    "  flop u4(q2, a, b);\n"
    "  gated u5(q3, a, b, en);\n"
    "  hold u6(q4, a);\n"
    "endmodule\n";

TEST_F(UdpRulesOfARun, OneDefinitionAppearsOnceForInstancesAtEveryDepth) {
  Run("primitive inv(o, a);\n"
      "  output o; input a;\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module leaf; wire x, y; inv i1(x, y); inv i2(y, x); endmodule\n"
      "module mid; leaf l1(); leaf l2(); endmodule\n"
      "module top; wire a, b, c, d;\n"
      "  inv u1(a, b); inv u2(c, d);\n"
      "  leaf l(); mid m();\n"
      "endmodule\n");
  EXPECT_EQ(NamesOf(vpiUdpDefn, nullptr), (std::vector<std::string>{"inv"}));
}

TEST_F(UdpRulesOfARun, EveryKindOfUdpReportsItsDefName) {
  Run(kKinds);
  for (const char* name :
       {"ansi_or", "proto_and", "latch", "flop", "gated", "hold"}) {
    vpiHandle defn = Defn(name);
    ASSERT_NE(defn, nullptr) << name;
    EXPECT_STREQ(vpi_get_str(vpiDefName, defn), name);
  }
  EXPECT_EQ(NamesOf(vpiUdpDefn, nullptr),
            (std::vector<std::string>{"ansi_or", "flop", "gated", "hold",
                                      "latch", "proto_and"}));
}

TEST_F(UdpRulesOfARun, ADefnsSizeCountsItsInputsOnly) {
  Run(kKinds);
  EXPECT_EQ(vpi_get(vpiSize, Defn("ansi_or")), 3);
  EXPECT_EQ(vpi_get(vpiSize, Defn("proto_and")), 2);
  EXPECT_EQ(vpi_get(vpiSize, Defn("latch")), 2);
  EXPECT_EQ(vpi_get(vpiSize, Defn("gated")), 3);
  EXPECT_EQ(vpi_get(vpiSize, Defn("hold")), 1);
}

TEST_F(UdpRulesOfARun, EverySequentialUdpIsASequentialPrimitive) {
  Run(kKinds);
  EXPECT_EQ(vpi_get(vpiPrimType, Defn("latch")), vpiSeqPrim);
  EXPECT_EQ(vpi_get(vpiPrimType, Defn("flop")), vpiSeqPrim);
  EXPECT_EQ(vpi_get(vpiPrimType, Defn("gated")), vpiSeqPrim);
  EXPECT_EQ(vpi_get(vpiPrimType, Defn("hold")), vpiSeqPrim);
  EXPECT_EQ(vpi_get(vpiPrimType, Defn("ansi_or")), vpiCombPrim);
  EXPECT_EQ(vpi_get(vpiPrimType, Defn("proto_and")), vpiCombPrim);
}

TEST_F(UdpRulesOfARun, ATableEntrysSizeCountsItsSymbols) {
  Run(kKinds);
  EXPECT_EQ(RowSizesOf("ansi_or"), (std::vector<int>{4, 4, 4, 4}));
  EXPECT_EQ(RowSizesOf("proto_and"), (std::vector<int>{3, 3, 3}));
  EXPECT_EQ(RowSizesOf("latch"), (std::vector<int>{4, 4, 4}));
  EXPECT_EQ(RowSizesOf("flop"), (std::vector<int>{4, 4, 4}));
  EXPECT_EQ(RowSizesOf("gated"), (std::vector<int>{5, 5}));
  EXPECT_EQ(RowSizesOf("hold"), (std::vector<int>{3, 3}));
}

TEST_F(UdpRulesOfARun, ASequentialUdpWithNoInitialReachesNone) {
  Run(kKinds);
  ASSERT_NE(Defn("hold"), nullptr);
  EXPECT_EQ(vpi_handle(vpiInitial, Defn("hold")), nullptr);
  EXPECT_EQ(vpi_handle(vpiInitial, Defn("latch")), nullptr);
  EXPECT_EQ(vpi_handle(vpiInitial, Defn("gated")), nullptr);
  EXPECT_NE(vpi_handle(vpiInitial, Defn("flop")), nullptr);
}

TEST_F(UdpRulesOfARun, EveryObjectOfAUdpReportsItsType) {
  Run(kKinds);
  const std::vector<vpiHandle> kDefns = ObjectsOf(vpiUdpDefn, nullptr);
  ASSERT_EQ(kDefns.size(), 6u);
  for (vpiHandle defn : kDefns) {
    EXPECT_EQ(vpi_get(vpiType, defn), vpiUdpDefn);
    const std::vector<vpiHandle> kRows = ObjectsOf(vpiTableEntry, defn);
    ASSERT_FALSE(kRows.empty());
    for (vpiHandle row : kRows) {
      EXPECT_EQ(vpi_get(vpiType, row), vpiTableEntry);
    }
    const std::vector<vpiHandle> kIos = ObjectsOf(vpiIODecl, defn);
    EXPECT_EQ(static_cast<int>(kIos.size()), vpi_get(vpiSize, defn) + 1);
    for (vpiHandle io : kIos) EXPECT_EQ(vpi_get(vpiType, io), vpiIODecl);
  }
}

TEST_F(UdpRulesOfARun, ATableEntryRefusesEveryOtherValueFormat) {
  Run(kKinds);
  const std::vector<vpiHandle> kRows = ObjectsOf(vpiTableEntry, Defn("flop"));
  ASSERT_FALSE(kRows.empty());
  for (const int kFormat : {vpiDecStrVal, vpiTimeVal, vpiStrengthVal}) {
    s_vpi_time time = {};
    s_vpi_strengthval strength = {};
    s_vpi_value value = {};
    value.format = kFormat;
    if (kFormat == vpiTimeVal) value.value.time = &time;
    if (kFormat == vpiStrengthVal) value.value.strength = &strength;
    vpi_get_value(kRows[0], &value);
    s_vpi_error_info info = {};
    const PLI_INT32 kLevel = vpi_chk_error(&info);
    EXPECT_EQ(kLevel, vpiError) << "format " << kFormat;
  }
}

constexpr std::string_view kSealedKey = "udp-rules-exchange-key";

TEST_F(UdpRulesOfARun, AProtectedUdpRefusesItsProtectedProperty) {
  RunUnderKey(EncryptEnvelopes("`pragma protect begin\n"
                               "primitive sealed_and(o, a, b);\n"
                               "  output o; input a, b;\n"
                               "  table 0 ? : 0; ? 0 : 0; 1 1 : 1; endtable\n"
                               "endprimitive\n"
                               "`pragma protect end\n"
                               "module t;\n"
                               "  wire o;\n"
                               "  sealed_and u1(o, 1'b1, 1'b0);\n"
                               "endmodule\n",
                               kSealedKey),
              kSealedKey, f_);
  const std::vector<vpiHandle> kDefns = ObjectsOf(vpiUdpDefn, nullptr);
  ASSERT_EQ(kDefns.size(), 1u);
  EXPECT_EQ(vpi_get(vpiIsProtected, kDefns[0]), 1);
  vpi_get(vpiProtected, kDefns[0]);
  s_vpi_error_info info = {};
  const PLI_INT32 kLevel = vpi_chk_error(&info);
  EXPECT_EQ(kLevel, vpiError);
  EXPECT_EQ(vpi_get(vpiType, kDefns[0]), vpiUdpDefn);
}

}  // namespace
}  // namespace delta
