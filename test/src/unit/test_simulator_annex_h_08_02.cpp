#include <dlfcn.h>
#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>
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

void PassVectorsToAnExport() {
  auto shift = NamedExport<void (*)(const svBitVecVal*, svBitVecVal*,
                                    const svLogicVecVal*, svLogicVecVal*)>(
      "shift_vectors");
  if (shift == nullptr) return;
  const svBitVecVal kBits[2] = {0x80000001U, 0x12U};
  const svLogicVecVal kLogic[2] = {{0xFF00U, 0x0FF0U}, {0xABU, 0x80U}};
  svBitVecVal bits[2] = {0, 0};
  svLogicVecVal logic[2] = {{0, 0}, {0, 0}};
  shift(kBits, bits, kLogic, logic);
  SeeInC({bits[0], bits[1] & 0xFFU, logic[0].aval, logic[0].bval,
          logic[1].aval & 0xFFU, logic[1].bval & 0xFFU});
}

void PassIntegerAndTimeToAnExport() {
  auto shift = NamedExport<void (*)(const svLogicVecVal*, svLogicVecVal*,
                                    const svLogicVecVal*, svLogicVecVal*)>(
      "shift_integer_and_time");
  if (shift == nullptr) return;
  const svLogicVecVal kInteger = {0xF5U, 0xF0U};
  const svLogicVecVal kTime[2] = {{7, 0}, {5, 0}};
  svLogicVecVal integer = {0, 0};
  svLogicVecVal time[2] = {{0, 0}, {0, 0}};
  shift(&kInteger, &integer, kTime, time);
  SeeInC({integer.aval, integer.bval, time[0].aval, time[0].bval, time[1].aval,
          time[1].bval});
}

void PassSmallInoutsToAnExport() {
  auto change = NamedExport<void (*)(int*, char*)>("change_small");
  if (change == nullptr) return;
  int number = 21;
  char byte = 5;
  change(&number, &byte);
  SeeInC({number, static_cast<signed char>(byte)});
}

void PassRealsToAnExport() {
  auto take =
      NamedExport<void (*)(double, float, double*, float*)>("take_reals");
  if (take == nullptr) return;
  double real = 0;
  float shortreal = 0;
  take(2.25, 0.75F, &real, &shortreal);
  SeeInC({static_cast<long long>(real * 4),
          static_cast<long long>(shortreal * 4)});
}

void PassIntegersToAnExport() {
  auto take =
      NamedExport<void (*)(char, short, long long, char*, short*, long long*)>(
          "take_integers");
  if (take == nullptr) return;
  char byte = 0;
  short shortint = 0;
  long long longint = 0;
  take(-5, -300, 5000000000LL, &byte, &shortint, &longint);
  SeeInC({static_cast<signed char>(byte), shortint, longint});
}

void PassScalarsAndAHandleToAnExport() {
  auto take =
      NamedExport<void (*)(void*, svBit, svLogic, void**, svBit*, svLogic*)>(
          "take_scalars");
  if (take == nullptr) return;
  int cell = 0;
  void* handle = nullptr;
  svBit bit = 0;
  svLogic logic = 0;
  take(&cell, 1, sv_z, &handle, &bit, &logic);
  SeeInC({handle == &cell ? 1 : 0, bit, logic});
}

void PassAnArrayToAnExport() {
  auto join = NamedExport<int (*)(const int*)>("join_three");
  if (join == nullptr) return;
  const int kThree[3] = {1, 2, 3};
  SeeInC({join(kThree)});
}

void RunCallerOfExports(const std::string& items, SimFixture& f) {
  RunModuleWithC(items, f,
                 {{"pass_vectors", CAddress(&PassVectorsToAnExport)},
                  {"pass_integer", CAddress(&PassIntegerAndTimeToAnExport)},
                  {"pass_inouts", CAddress(&PassSmallInoutsToAnExport)},
                  {"pass_reals", CAddress(&PassRealsToAnExport)},
                  {"pass_integers", CAddress(&PassIntegersToAnExport)},
                  {"pass_scalars", CAddress(&PassScalarsAndAHandleToAnExport)},
                  {"pass_array", CAddress(&PassAnArrayToAnExport)}},
                 "annex_h_08_02_formals");
}

TEST(DpiExportFormalTypes, PackedVectorsCrossBothWays) {
  SimFixture f;
  RunCallerOfExports(
      "  export \"DPI-C\" function shift_vectors;\n"
      "  import \"DPI-C\" context function void pass_vectors();\n"
      "  function void shift_vectors(input bit [39:0] a,\n"
      "      output bit [39:0] b, input logic [39:0] c,\n"
      "      output logic [39:0] d);\n"
      "    b = a << 1; d = c << 4;\n"
      "  endfunction\n"
      "  initial pass_vectors();\n",
      f);
  EXPECT_EQ(SeenInC(),
            (std::vector<long long>{2, 0x25, 0xFF000, 0xFF00, 0xB0, 0}));
}

TEST(DpiExportFormalTypes, AnIntegerAndATimeCrossBothWays) {
  SimFixture f;
  RunCallerOfExports(
      "  export \"DPI-C\" function shift_integer_and_time;\n"
      "  import \"DPI-C\" context function void pass_integer();\n"
      "  function void shift_integer_and_time(input integer i,\n"
      "      output integer oi, input time t, output time ot);\n"
      "    oi = i << 1; ot = t + 64'h1_0000_0002;\n"
      "  endfunction\n"
      "  initial pass_integer();\n",
      f);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{0x1EA, 0x1E0, 9, 0, 6, 0}));
}

TEST(DpiExportFormalTypes, AnInoutOfASmallTypeCrossesInAndBack) {
  SimFixture f;
  RunCallerOfExports(
      "  export \"DPI-C\" function change_small;\n"
      "  import \"DPI-C\" context function void pass_inouts();\n"
      "  function void change_small(inout int n, inout byte b);\n"
      "    n = n * 2; b = -b;\n"
      "  endfunction\n"
      "  initial pass_inouts();\n",
      f);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{42, -5}));
}

TEST(DpiExportFormalTypes, IntegersCrossBothWays) {
  SimFixture f;
  RunCallerOfExports(
      "  export \"DPI-C\" function take_integers;\n"
      "  import \"DPI-C\" context function void pass_integers();\n"
      "  function void take_integers(input byte b, input shortint h,\n"
      "      input longint l, output byte bo, output shortint ho,\n"
      "      output longint lo);\n"
      "    bo = b - 1; ho = h - 1; lo = l + 1;\n"
      "  endfunction\n"
      "  initial pass_integers();\n",
      f);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{-6, -301, 5000000001LL}));
}

TEST(DpiExportFormalTypes, DISABLED_RealsCrossBothWays) {
  SimFixture f;
  RunCallerOfExports(
      "  export \"DPI-C\" function take_reals;\n"
      "  import \"DPI-C\" context function void pass_reals();\n"
      "  function void take_reals(input real r, input shortreal s,\n"
      "      output real ro, output shortreal so);\n"
      "    ro = r * 2; so = s + 1;\n"
      "  endfunction\n"
      "  initial pass_reals();\n",
      f);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{18, 7}));
}

TEST(DpiExportFormalTypes, ScalarsAndAHandleCrossBothWays) {
  SimFixture f;
  RunCallerOfExports(
      "  export \"DPI-C\" function take_scalars;\n"
      "  import \"DPI-C\" context function void pass_scalars();\n"
      "  function void take_scalars(input chandle c, input bit b,\n"
      "      input logic l, output chandle co, output bit bo,\n"
      "      output logic lo);\n"
      "    co = c; bo = b; lo = l;\n"
      "  endfunction\n"
      "  initial pass_scalars();\n",
      f);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{1, 1, sv_z}));
}

TEST(DpiExportFormalTypes, ASizedUnpackedArrayCrossesIn) {
  SimFixture f;
  RunCallerOfExports(
      "  export \"DPI-C\" function join_three;\n"
      "  import \"DPI-C\" context function void pass_array();\n"
      "  function int join_three(input int a[3]);\n"
      "    return a[0] * 100 + a[1] * 10 + a[2];\n"
      "  endfunction\n"
      "  initial pass_array();\n",
      f);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{123}));
}

using WidenInC = void (*)(const svBitVecVal*, svLogicVecVal*);

void WidenAsAnImport(const svBitVecVal* a, svLogicVecVal* b) {
  b[0] = {a[0], 1};
  b[1] = {a[1], 0x80U};
}

void CallBothWideners() {
  const WidenInC kImport = &WidenAsAnImport;
  const auto kExport = NamedExport<WidenInC>("widen_export");
  if (kExport == nullptr) return;
  const svBitVecVal kBits[2] = {0x5U, 0x9U};
  for (const WidenInC kWiden : {kImport, kExport}) {
    svLogicVecVal logic[2] = {{0, 0}, {0, 0}};
    kWiden(kBits, logic);
    SeeInC({logic[0].aval, logic[0].bval, logic[1].aval & 0xFFU,
            logic[1].bval & 0xFFU});
  }
}

TEST(DpiCallsFromC, OnePrototypeCallsAnImportAndAnExportOfTheSameFormals) {
  SimFixture f;
  RunModuleWithC(
      "  export \"DPI-C\" function widen_export;\n"
      "  import \"DPI-C\" function void widen_import(\n"
      "      input bit [39:0] a, output logic [39:0] b);\n"
      "  import \"DPI-C\" context function void call_both();\n"
      "  function void widen_export(input bit [39:0] a,\n"
      "      output logic [39:0] b);\n"
      "    b = a; b[0] = 1'bx; b[39] = 1'bz;\n"
      "  endfunction\n"
      "  logic [39:0] r;\n"
      "  initial begin\n"
      "    widen_import(40'h05_0000_0003, r);\n"
      "    call_both();\n"
      "  end\n",
      f,
      {{"widen_import", CAddress(&WidenAsAnImport)},
       {"call_both", CAddress(&CallBothWideners)}},
      "annex_h_08_02_one_prototype");
  EXPECT_EQ(SeenInC(), (std::vector<long long>{5, 1, 9, 0x80, 5, 1, 9, 0x80}));
}

}  // namespace
