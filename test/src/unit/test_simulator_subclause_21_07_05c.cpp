#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_vcd_dump_run.h"
#include "helpers_vcd_var_decl.h"

namespace delta {
namespace {

class VcdMappingOfComposedTypes : public VcdDumpRunTestBase {
 protected:
  std::string Dump(const std::string& items) {
    return RunVcdDump(
        "module t;\n" + items +
            "  initial begin\n"
            "    $dumpvars;\n"
            "    #1;\n"
            "  end\n"
            "endmodule\n",
        {.scope = "t",
         .registration = VcdSignalRegistration::kContextFiltered});
  }

  static std::string Mapped(const std::string& content, std::string_view name) {
    auto decl = VarDecl(content, name);
    if (decl.empty()) return "<not dumped>";
    return decl[1] + " " + decl[2];
  }
};

TEST_F(VcdMappingOfComposedTypes, EveryPackedDimensionCollapsesIntoOne) {
  auto content = Dump(
      "  logic [1:0][2:0][3:0] cube;\n"
      "  bit [1:0][3:0] square;\n");
  EXPECT_EQ(Mapped(content, "cube"), "reg 24") << content;
  EXPECT_EQ(Mapped(content, "square"), "reg 8") << content;
}

TEST_F(VcdMappingOfComposedTypes, APackedStructOfPackedPartsIsOneVector) {
  auto content = Dump(
      "  struct packed {\n"
      "    logic [1:0][3:0] a;\n"
      "    struct packed { bit x; byte y; } inner;\n"
      "  } s;\n");
  EXPECT_EQ(Mapped(content, "s"), "reg 17") << content;
  EXPECT_EQ(Mapped(content, "inner"), "<not dumped>") << content;
}

TEST_F(VcdMappingOfComposedTypes, AnEnumIsDumpedAsItsBaseType) {
  auto content = Dump(
      "  enum int {I0, I1} e_int;\n"
      "  enum shortint {S0, S1} e_short;\n"
      "  enum longint {L0, L1} e_long;\n"
      "  enum logic [2:0] {G0, G1} e_logic;\n"
      "  enum bit {B0, B1} e_bit;\n");
  EXPECT_EQ(Mapped(content, "e_int"), "integer 32") << content;
  EXPECT_EQ(Mapped(content, "e_short"), "reg 16") << content;
  EXPECT_EQ(Mapped(content, "e_long"), "reg 64") << content;
  EXPECT_EQ(Mapped(content, "e_logic"), "reg 3") << content;
  EXPECT_EQ(Mapped(content, "e_bit"), "reg 1") << content;
}

TEST_F(VcdMappingOfComposedTypes, UnpackedStructMembersTakeTheirOwnMapping) {
  auto content = Dump(
      "  struct {\n"
      "    longint l;\n"
      "    shortint h;\n"
      "    enum {X, Y} e;\n"
      "    logic [1:0][1:0] p;\n"
      "  } u;\n");
  EXPECT_EQ(Mapped(content, "l"), "reg 64") << content;
  EXPECT_EQ(Mapped(content, "h"), "reg 16") << content;
  EXPECT_EQ(Mapped(content, "e"), "integer 32") << content;
  EXPECT_EQ(Mapped(content, "p"), "reg 4") << content;
}

TEST_F(VcdMappingOfComposedTypes, DISABLED_AShortrealMemberIsDumpedAsReal) {
  auto content = Dump("  struct { shortreal f; } u;\n");
  EXPECT_EQ(Mapped(content, "f").substr(0, 4), "real") << content;
}

TEST_F(VcdMappingOfComposedTypes, DISABLED_APackedStructMemberIsOneVector) {
  auto content = Dump("  struct { struct packed { bit a; bit b; } ps; } u;\n");
  EXPECT_EQ(Mapped(content, "ps"), "reg 2") << content;
  EXPECT_EQ(content.find("$scope fork ps"), std::string::npos) << content;
}

TEST_F(VcdMappingOfComposedTypes, ANestedUnpackedStructIsANestedForkScope) {
  auto content = Dump(
      "  struct {\n"
      "    int a;\n"
      "    struct { byte b; } inner;\n"
      "  } outer;\n");
  auto outer = content.find("$scope fork outer $end");
  auto inner = content.find("$scope fork inner $end");
  auto member = content.find(" b $end");
  ASSERT_NE(outer, std::string::npos) << content;
  ASSERT_NE(inner, std::string::npos) << content;
  EXPECT_LT(outer, inner) << content;
  EXPECT_LT(inner, member) << content;
  EXPECT_EQ(Mapped(content, "b"), "reg 8") << content;
  EXPECT_EQ(Mapped(content, "inner"), "<not dumped>") << content;
}

TEST_F(VcdMappingOfComposedTypes, DISABLED_AnUnpackedArrayMemberIsNotDumped) {
  auto content = Dump("  struct { int a; int arr [2]; } s;\n");
  EXPECT_EQ(Mapped(content, "a"), "integer 32") << content;
  EXPECT_EQ(Mapped(content, "arr"), "<not dumped>") << content;
}

TEST_F(VcdMappingOfComposedTypes, UnpackedArraysOfEveryKindAreNotDumped) {
  auto content = Dump(
      "  int kept;\n"
      "  int dyn [];\n"
      "  int assoc [int];\n"
      "  logic [3:0] grid [2][3];\n"
      "  struct { int a; } recs [2];\n");
  EXPECT_EQ(Mapped(content, "kept"), "integer 32") << content;
  for (const char* name : {"dyn", "assoc", "grid", "recs", "a"}) {
    EXPECT_EQ(Mapped(content, name), "<not dumped>") << name << "\n" << content;
  }
  EXPECT_EQ(content.find("$scope fork recs"), std::string::npos) << content;
}

TEST_F(VcdMappingOfComposedTypes, DISABLED_AQueueIsNotDumped) {
  auto content = Dump(
      "  int kept;\n"
      "  int q [$];\n");
  EXPECT_EQ(Mapped(content, "kept"), "integer 32") << content;
  EXPECT_EQ(Mapped(content, "q"), "<not dumped>") << content;
}

TEST_F(VcdMappingOfComposedTypes, AutomaticVariablesAreNotDumped) {
  auto content = Dump(
      "  int kept;\n"
      "  task automatic tk;\n"
      "    int task_local;\n"
      "    task_local = 1;\n"
      "  endtask\n"
      "  initial begin : blk\n"
      "    automatic int block_local = 1;\n"
      "    tk();\n"
      "  end\n");
  EXPECT_EQ(Mapped(content, "kept"), "integer 32") << content;
  EXPECT_EQ(Mapped(content, "task_local"), "<not dumped>") << content;
  EXPECT_EQ(Mapped(content, "block_local"), "<not dumped>") << content;
}

}  // namespace
}  // namespace delta
