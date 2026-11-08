#include <dlfcn.h>
#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"

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

TEST(DpiCallsFromC, AnExportHasTheHeaderAnImportWithTheSameListHas) {
  const std::vector<DpiArg> kFormals = {
      Formal("a", DataTypeKind::kInt, Direction::kInput),
      Formal("b", DataTypeKind::kBit, Direction::kOutput, 8),
      Formal("c", DataTypeKind::kLogic, Direction::kInput, 40)};
  EXPECT_EQ(DpiCFunctionHeader("f", DataTypeKind::kInt, kFormals),
            "int f(const int a, svBitVecVal* b, const svLogicVecVal* c)");
  EXPECT_EQ(
      DpiCHeaderOfExportedSubroutine("f", DataTypeKind::kInt, kFormals, false),
      DpiCFunctionHeader("f", DataTypeKind::kInt, kFormals));
  EXPECT_EQ(DpiCHeaderOfExportedSubroutine("g", DataTypeKind::kVoid, {}, false),
            "void g()");
  EXPECT_EQ(DpiCFunctionHeader("g", DataTypeKind::kVoid, {}), "void g()");
}

TEST(DpiCallsFromC, AnExportedTaskReturnsAnInt) {
  const std::vector<DpiArg> kFormals = {
      Formal("a", DataTypeKind::kInt, Direction::kInput)};
  EXPECT_EQ(
      DpiCHeaderOfExportedSubroutine("t", DataTypeKind::kVoid, kFormals, true),
      "int t(const int a)");
  EXPECT_EQ(DpiCTypeOfExportedTaskResult(), "int");
}

TEST(DpiCallsFromC, AnExportCannotHaveAnOpenArrayFormal) {
  EXPECT_FALSE(DpiExportFormalMayBeAnOpenArray());
  EXPECT_TRUE(DpiExportFormalMayHaveType(DataTypeKind::kInt));
  EXPECT_TRUE(DpiExportFormalMayHaveType(DataTypeKind::kBit));
  EXPECT_TRUE(DpiExportFormalMayHaveType(DataTypeKind::kString));
  EXPECT_FALSE(DpiExportFormalMayHaveType(DataTypeKind::kEvent));
}

TEST(DpiCallsFromC, TheCallerAllocatesAnActualPassedByReference) {
  EXPECT_EQ(DpiSideAllocatingActualOfExportCall(), DpiMemorySide::kC);
  EXPECT_EQ(DpiRepresentationOfFormal(
                Formal("b", DataTypeKind::kBit, Direction::kOutput, 8)),
            DpiRepresentation::kCanonical);
}

struct Pair {
  int x;
  int y;
};

template <typename Function>
Function ExportNamed(const char* name) {
  return reinterpret_cast<Function>(dlsym(RTLD_DEFAULT, name));
}

int TakeAPair() {
  auto take = ExportNamed<int (*)(const Pair*)>("take");
  if (take == nullptr) return -1;
  const Pair kPair = {4, 7};
  return take(&kPair);
}

int MakeAPair() {
  auto make = ExportNamed<void (*)(Pair*)>("make");
  if (make == nullptr) return -1;
  Pair pair = {0, 0};
  make(&pair);
  return (pair.x * 10) + pair.y;
}

uint64_t VariableValue(SimFixture& f, std::string_view name) {
  auto* var = f.ctx.FindVariable(name);
  return var == nullptr ? ~uint64_t{0} : var->value.ToUint64();
}

TEST(DpiCallsFromC, AnExportTakesAnUnpackedStructFormal) {
  SimFixture f;
  RunWithImportsBound(
      "module top;\n"
      "  typedef struct { int x; int y; } pair;\n"
      "  export \"DPI-C\" function take;\n"
      "  export \"DPI-C\" function make;\n"
      "  import \"DPI-C\" context function int take_a_pair();\n"
      "  import \"DPI-C\" context function int make_a_pair();\n"
      "  function int take(input pair p); return p.x * 10 + p.y; endfunction\n"
      "  function void make(output pair q); q.x = 3; q.y = 8; endfunction\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    r1 = take_a_pair();\n"
      "    r2 = make_a_pair();\n"
      "  end\n"
      "endmodule\n",
      f,
      {{"take_a_pair", reinterpret_cast<void*>(&TakeAPair)},
       {"make_a_pair", reinterpret_cast<void*>(&MakeAPair)}},
      "annex_h_08_02_export_struct");
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(VariableValue(f, "r1"), 47U);
  EXPECT_EQ(VariableValue(f, "r2"), 38U);
}

}  // namespace
