#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/svdpi.h"

using namespace delta;

namespace {

DpiArg Formal(const char* name, DataTypeKind type, Direction direction,
              uint32_t width = 0) {
  DpiArg formal;
  formal.name = name;
  formal.type = type;
  formal.direction = direction;
  formal.width = width;
  return formal;
}

TEST(DpiExportActualAllocation, TheCallerAllocatesWhatIsPassedByReference) {
  EXPECT_TRUE(DpiCallerAllocatesExportActual(
      Formal("o", DataTypeKind::kInt, Direction::kOutput)));
  EXPECT_TRUE(DpiCallerAllocatesExportActual(
      Formal("io", DataTypeKind::kReal, Direction::kInout)));
  EXPECT_TRUE(DpiCallerAllocatesExportActual(
      Formal("v", DataTypeKind::kBit, Direction::kInput, 8)));
  EXPECT_FALSE(DpiCallerAllocatesExportActual(
      Formal("i", DataTypeKind::kInt, Direction::kInput)));
  EXPECT_FALSE(DpiCallerAllocatesExportActual(
      Formal("s", DataTypeKind::kString, Direction::kInput)));
}

TEST(DpiExportActualAllocation, APackedActualIsACArrayOfCanonicalChunks) {
  EXPECT_EQ(DpiCAllocationOfExportActual(
                Formal("o", DataTypeKind::kInt, Direction::kOutput)),
            "int o");
  EXPECT_EQ(DpiCAllocationOfExportActual(
                Formal("io", DataTypeKind::kReal, Direction::kInout)),
            "double io");
  EXPECT_EQ(DpiCAllocationOfExportActual(
                Formal("v", DataTypeKind::kBit, Direction::kInput, 8)),
            "svBitVecVal v[1]");
  EXPECT_EQ(DpiCAllocationOfExportActual(
                Formal("w", DataTypeKind::kLogic, Direction::kOutput, 40)),
            "svLogicVecVal w[2]");
  EXPECT_EQ(DpiCAllocationOfExportActual(
                Formal("t", DataTypeKind::kTime, Direction::kInout)),
            "svLogicVecVal t[2]");
  EXPECT_EQ(DpiCAllocationOfExportActual(
                Formal("e", DataTypeKind::kEvent, Direction::kInput)),
            "");
}

void AllocateABitInput() {
  auto see = NamedExport<void (*)(const svBitVecVal*)>("see_bits");
  if (see == nullptr) return;
  const svBitVecVal kBits[2] = {0xDEADBEEFU, 0xC5U};
  see(kBits);
}

void AllocateALogicInput() {
  auto see = NamedExport<void (*)(const svLogicVecVal*)>("see_logic");
  if (see == nullptr) return;
  const svLogicVecVal kLogic[2] = {{0x3U, 0x5U}, {0x81U, 0x80U}};
  see(kLogic);
}

void AllocateABitOutput() {
  auto give = NamedExport<void (*)(svBitVecVal*)>("give_bits");
  if (give == nullptr) return;
  svBitVecVal bits[3] = {0, 0, 0};
  give(bits);
  SeeInC({bits[0], bits[1], bits[2] & 0x3FU});
}

void AllocateALogicOutputAndInouts() {
  auto give =
      NamedExport<void (*)(svLogicVecVal*, svLogicVecVal*, svBitVecVal*)>(
          "give_logic");
  if (give == nullptr) return;
  svLogicVecVal output[2] = {{0, 0}, {0, 0}};
  svLogicVecVal logic[2] = {{0x10U, 0x20U}, {0x7U, 0x4U}};
  svBitVecVal bits[2] = {0xFFFFFFFFU, 0x1U};
  give(output, logic, bits);
  SeeInC({output[0].aval, output[0].bval, output[1].aval & 0xFFU,
          output[1].bval & 0xFFU});
  SeeInC({logic[0].aval, logic[0].bval, logic[1].aval & 0xFFU,
          logic[1].bval & 0xFFU});
  SeeInC({bits[0], bits[1] & 0xFFU});
}

void RunAllocators(const std::string& items, SimFixture& f) {
  RunModuleWithC(items, f,
                 {{"bit_input", CAddress(&AllocateABitInput)},
                  {"logic_input", CAddress(&AllocateALogicInput)},
                  {"bit_output", CAddress(&AllocateABitOutput)},
                  {"logic_output", CAddress(&AllocateALogicOutputAndInouts)}},
                 "annex_h_08_05_allocated");
}

TEST(DpiExportActualAllocation, AnExportReadsEveryChunkOfABitInput) {
  SimFixture f;
  RunAllocators(
      "  export \"DPI-C\" function see_bits;\n"
      "  import \"DPI-C\" context function void bit_input();\n"
      "  bit [39:0] seen;\n"
      "  function void see_bits(input bit [39:0] b); seen = b; endfunction\n"
      "  initial bit_input();\n",
      f);
  EXPECT_EQ(DesignValue(f, "seen"), 0xC5DEADBEEFULL);
}

TEST(DpiExportActualAllocation, AnExportReadsTheUnknownBitsOfALogicInput) {
  SimFixture f;
  RunAllocators(
      "  export \"DPI-C\" function see_logic;\n"
      "  import \"DPI-C\" context function void logic_input();\n"
      "  bit same;\n"
      "  function void see_logic(input logic [39:0] l);\n"
      "    same = l === {8'bx0000001, 29'b0, 3'bz1x};\n"
      "  endfunction\n"
      "  initial logic_input();\n",
      f);
  EXPECT_EQ(DesignValue(f, "same"), 1U);
}

TEST(DpiExportActualAllocation, AnExportWritesEveryChunkOfABitOutput) {
  SimFixture f;
  RunAllocators(
      "  export \"DPI-C\" function give_bits;\n"
      "  import \"DPI-C\" context function void bit_output();\n"
      "  function void give_bits(output bit [69:0] b);\n"
      "    b = {6'h2a, 32'h89abcdef, 32'h01234567};\n"
      "  endfunction\n"
      "  initial bit_output();\n",
      f);
  EXPECT_EQ(SeenInC(),
            (std::vector<long long>{0x01234567, 0x89ABCDEFLL, 0x2A}));
}

TEST(DpiExportActualAllocation, AnExportWritesALogicOutputAndPackedInouts) {
  SimFixture f;
  RunAllocators(
      "  export \"DPI-C\" function give_logic;\n"
      "  import \"DPI-C\" context function void logic_output();\n"
      "  function void give_logic(output logic [39:0] o,\n"
      "      inout logic [39:0] l, inout bit [39:0] b);\n"
      "    o = 40'hx1_0000_00z2; l = l << 1; b = b + 1;\n"
      "  endfunction\n"
      "  initial logic_output();\n",
      f);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{0x02, 0xF0, 0xF1, 0xF0, 0x20,
                                               0x40, 0xE, 0x8, 0, 2}));
}

}  // namespace
