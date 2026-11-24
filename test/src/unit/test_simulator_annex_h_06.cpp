#include <gtest/gtest.h>

#include <cstdint>
#include <map>
#include <string>

#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/svdpi.h"

using namespace delta;

namespace {

DpiArg Formal(DataTypeKind type, Direction direction, uint32_t width = 0) {
  DpiArg formal;
  formal.name = "a";
  formal.type = type;
  formal.direction = direction;
  formal.width = width;
  return formal;
}

TEST(DpiSemanticConstraints, TheCallerCoercesAPackedActualToTheFormalsWidth) {
  EXPECT_EQ(DpiCoercionOfPackedActual(40, 32), DpiActualCoercion::kTruncate);
  EXPECT_EQ(DpiCoercionOfPackedActual(8, 16), DpiActualCoercion::kExtend);
  EXPECT_EQ(DpiCoercionOfPackedActual(16, 16), DpiActualCoercion::kNone);
  EXPECT_EQ(DpiCoercionOfPackedActual(33, 32), DpiActualCoercion::kTruncate);
  EXPECT_EQ(DpiCoercionOfPackedActual(32, 33), DpiActualCoercion::kExtend);
}

TEST(DpiSemanticConstraints, TheCTypeShallMatchTheFormalsType) {
  const DpiArg kIntIn = Formal(DataTypeKind::kInt, Direction::kInput);
  EXPECT_TRUE(DpiCTypeMatchesFormal(kIntIn, false, "const int"));
  EXPECT_FALSE(DpiCTypeMatchesFormal(kIntIn, false, "unsigned int"));
  const DpiArg kIntOut = Formal(DataTypeKind::kInt, Direction::kOutput);
  EXPECT_TRUE(DpiCTypeMatchesFormal(kIntOut, false, "int*"));
  EXPECT_TRUE(DpiCTypeMatchesFormal(kIntOut, false, "int *"));
  EXPECT_FALSE(DpiCTypeMatchesFormal(kIntOut, false, "const int"));
  const DpiArg kBitsIn = Formal(DataTypeKind::kBit, Direction::kInput, 8);
  EXPECT_TRUE(DpiCTypeMatchesFormal(kBitsIn, false, "const svBitVecVal *"));
  EXPECT_FALSE(DpiCTypeMatchesFormal(kBitsIn, false, "const unsigned char"));
  const DpiArg kBitsOut = Formal(DataTypeKind::kBit, Direction::kOutput, 8);
  EXPECT_TRUE(DpiCTypeMatchesFormal(kBitsOut, false, "svBitVecVal*"));
  EXPECT_FALSE(DpiCTypeMatchesFormal(kBitsOut, false, "svLogicVecVal*"));
  EXPECT_TRUE(DpiCTypeMatchesFormal(kBitsOut, true, "const svOpenArrayHandle"));
  EXPECT_FALSE(DpiCTypeMatchesFormal(kBitsOut, true, "svBitVecVal*"));
}

struct Received {
  int as_int = 0;
  double as_real = 0.0;
  uint32_t as_bits = 0;
  int calls = 0;
};

Received& LastReceived() {
  static Received received;
  return received;
}

void TakeInoutInt(int* value) {
  LastReceived().as_int = *value;
  *value = 0x1234;
}

void TakeReal(double value) { LastReceived().as_real = value; }

void TakeInt(int value) {
  LastReceived().as_int = value;
  ++LastReceived().calls;
}

void TakeBits(const svBitVecVal* value) { LastReceived().as_bits = value[0]; }

int TaskTakeInt(int value) {
  TakeInt(value);
  return 0;
}

int TaskTakeReal(double value) {
  TakeReal(value);
  return 0;
}

int TaskTakeBits(const svBitVecVal* value) {
  TakeBits(value);
  return 0;
}

void GiveUnknownBits(svLogicVecVal* value) {
  value[0].aval = 0xCU;
  value[0].bval = 0x6U;
}

int TaskGiveUnknownBits(svLogicVecVal* value) {
  GiveUnknownBits(value);
  return 0;
}

std::map<std::string, void*> Takers() {
  return {{"take_inout", reinterpret_cast<void*>(&TakeInoutInt)},
          {"take_real", reinterpret_cast<void*>(&TakeReal)},
          {"take_int", reinterpret_cast<void*>(&TakeInt)},
          {"take_bits", reinterpret_cast<void*>(&TakeBits)},
          {"give_unknown", reinterpret_cast<void*>(&GiveUnknownBits)},
          {"task_int", reinterpret_cast<void*>(&TaskTakeInt)},
          {"task_real", reinterpret_cast<void*>(&TaskTakeReal)},
          {"task_bits", reinterpret_cast<void*>(&TaskTakeBits)},
          {"task_unknown", reinterpret_cast<void*>(&TaskGiveUnknownBits)}};
}

void RunTakers(const std::string& items, SimFixture& f) {
  LastReceived() = Received{};
  RunWithImportsBound("module t;\n" + items + "endmodule\n", f, Takers(),
                      "annex_h_06_takers");
  EXPECT_TRUE(f.diag.Diagnostics().empty());
}

TEST(DpiCallSiteCoercion, AnInoutActualIsCoercedInBothDirections) {
  SimFixture f;
  RunTakers(
      "  import \"DPI-C\" function void take_inout(inout int v);\n"
      "  logic [7:0] a = 8'h80;\n"
      "  initial take_inout(a);\n",
      f);
  EXPECT_EQ(LastReceived().as_int, 128);
  EXPECT_EQ(DesignValue(f, "a"), 0x34U);
}

TEST(DpiCallSiteCoercion, DISABLED_AnIntActualReachesARealFormalAsAReal) {
  SimFixture f;
  RunTakers(
      "  import \"DPI-C\" function void take_real(input real v);\n"
      "  int a = -3;\n"
      "  initial take_real(a);\n",
      f);
  EXPECT_EQ(LastReceived().as_real, -3.0);
}

TEST(DpiCallSiteCoercion, UnknownBitsOfAnOutputReachATwoStateActualAsZero) {
  SimFixture f;
  RunTakers(
      "  import \"DPI-C\" function void give_unknown(output logic [3:0] v);\n"
      "  int a = -1;\n"
      "  bit [3:0] b = 4'hf;\n"
      "  initial begin give_unknown(a); give_unknown(b); end\n",
      f);
  EXPECT_EQ(DesignValue(f, "a"), 8U);
  EXPECT_EQ(DesignValue(f, "b"), 8U);
}

TEST(DpiCallSiteCoercion, UnknownBitsOfAnInoutReachATwoStateActualAsZero) {
  SimFixture f;
  RunTakers(
      "  import \"DPI-C\" function void give_unknown(inout logic [3:0] v);\n"
      "  int a = -1;\n"
      "  bit [3:0] b = 4'hf;\n"
      "  initial begin give_unknown(a); give_unknown(b); end\n",
      f);
  EXPECT_EQ(DesignValue(f, "a"), 8U);
  EXPECT_EQ(DesignValue(f, "b"), 8U);
}

TEST(DpiCallSiteCoercion, AWiderPackedActualIsTruncated) {
  SimFixture f;
  RunTakers(
      "  import \"DPI-C\" function void take_bits(input bit [31:0] v);\n"
      "  bit [39:0] a = 40'hab_cdef_0123;\n"
      "  initial take_bits(a);\n",
      f);
  EXPECT_EQ(LastReceived().as_bits, 0xCDEF0123U);
}

TEST(DpiCallSiteCoercion, ANarrowerUnsignedPackedActualIsZeroExtended) {
  SimFixture f;
  RunTakers(
      "  import \"DPI-C\" function void take_bits(input bit [15:0] v);\n"
      "  bit [7:0] a = 8'hf0;\n"
      "  initial take_bits(a);\n",
      f);
  EXPECT_EQ(LastReceived().as_bits & 0xFFFFU, 0x00F0U);
}

TEST(DpiCallSiteCoercion, DISABLED_ANarrowerSignedPackedActualIsSignExtended) {
  SimFixture f;
  RunTakers(
      "  import \"DPI-C\" function void take_bits(input bit [15:0] v);\n"
      "  bit signed [7:0] a = 8'hf0;\n"
      "  initial take_bits(a);\n",
      f);
  EXPECT_EQ(LastReceived().as_bits & 0xFFFFU, 0xFFF0U);
}

TEST(DpiCallSiteCoercion, ATasksIntegerActualIsTruncated) {
  SimFixture f;
  RunTakers(
      "  import \"DPI-C\" task task_int(input int v);\n"
      "  longint a = 64'h1_0000_0007;\n"
      "  initial task_int(a);\n",
      f);
  EXPECT_EQ(LastReceived().as_int, 7);
}

TEST(DpiCallSiteCoercion, DISABLED_ATasksRealActualIsRounded) {
  SimFixture f;
  RunTakers(
      "  import \"DPI-C\" task task_int(input int v);\n"
      "  real a = 2.6;\n"
      "  initial task_int(a);\n",
      f);
  EXPECT_EQ(LastReceived().as_int, 3);
}

TEST(DpiCallSiteCoercion, DISABLED_ATasksIntActualReachesARealFormalAsAReal) {
  SimFixture f;
  RunTakers(
      "  import \"DPI-C\" task task_real(input real v);\n"
      "  int a = -3;\n"
      "  initial task_real(a);\n",
      f);
  EXPECT_EQ(LastReceived().as_real, -3.0);
}

TEST(DpiCallSiteCoercion, DISABLED_ATasksPackedActualIsTruncatedOrExtended) {
  SimFixture f;
  RunTakers(
      "  import \"DPI-C\" task task_bits(input bit [31:0] v);\n"
      "  bit [39:0] a = 40'hab_cdef_0123;\n"
      "  initial task_bits(a);\n",
      f);
  EXPECT_EQ(LastReceived().as_bits, 0xCDEF0123U);
  SimFixture g;
  RunTakers(
      "  import \"DPI-C\" task task_bits(input bit [15:0] v);\n"
      "  bit signed [7:0] a = 8'hf0;\n"
      "  initial task_bits(a);\n",
      g);
  EXPECT_EQ(LastReceived().as_bits & 0xFFFFU, 0xFFF0U);
}

TEST(DpiCallSiteCoercion, ATasksFourStateValuesReachTheTwoStateSideAsZero) {
  SimFixture f;
  RunTakers(
      "  import \"DPI-C\" task task_unknown(output logic [3:0] v);\n"
      "  import \"DPI-C\" task task_int(input int v);\n"
      "  int a = -1;\n"
      "  logic [3:0] l = 4'b1x0z;\n"
      "  initial begin task_unknown(a); task_int(l); end\n",
      f);
  EXPECT_EQ(DesignValue(f, "a"), 8U);
  EXPECT_EQ(LastReceived().as_int, 8);
}

TEST(DpiFormalsAsDeclared, AConstantActualIsStillPassed) {
  SimFixture f;
  RunTakers(
      "  import \"DPI-C\" function void take_int(input int v);\n"
      "  localparam int P = 6;\n"
      "  initial begin take_int(5); take_int(P); end\n",
      f);
  EXPECT_EQ(LastReceived().calls, 2);
  EXPECT_EQ(LastReceived().as_int, 6);
}

TEST(DpiFormalsAsDeclared, AnActualNeverReadAgainIsStillPassed) {
  SimFixture f;
  RunTakers(
      "  import \"DPI-C\" function void take_int(input int v);\n"
      "  import \"DPI-C\" function void take_bits(input bit [31:0] v);\n"
      "  initial begin\n"
      "    automatic int unread = 11;\n"
      "    automatic bit [31:0] bits = 32'h1234_5678;\n"
      "    take_int(unread);\n"
      "    take_bits(bits);\n"
      "  end\n",
      f);
  EXPECT_EQ(LastReceived().calls, 1);
  EXPECT_EQ(LastReceived().as_int, 11);
  EXPECT_EQ(LastReceived().as_bits, 0x12345678U);
}

TEST(DpiFormalsAsDeclared, AnOutputNeverReadIsStillPassedByAddress) {
  SimFixture f;
  RunTakers(
      "  import \"DPI-C\" function void take_inout(inout int v);\n"
      "  int unread = 3;\n"
      "  initial take_inout(unread);\n",
      f);
  EXPECT_EQ(LastReceived().as_int, 3);
}

int64_t ReturnWide() { return int64_t{-5} << 33; }

unsigned int ReturnUnsigned() { return 7U; }

TEST(DpiSemanticConstraints, AMatchingCResultTypeCarriesItsValue) {
  SimFixture f;
  RunWithImportsBound(
      "module t;\n"
      "  import \"DPI-C\" function longint give_wide();\n"
      "  longint r;\n"
      "  initial r = give_wide();\n"
      "endmodule\n",
      f, {{"give_wide", reinterpret_cast<void*>(&ReturnWide)}},
      "annex_h_06_result");
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(static_cast<int64_t>(DesignValue(f, "r")), int64_t{-5} << 33);
}

TEST(DpiSemanticConstraints, AMismatchedCPrototypeIsNotReported) {
  SimFixture f;
  RunWithImportsBound(
      "module t;\n"
      "  import \"DPI-C\" function int give_unsigned();\n"
      "  int r;\n"
      "  initial r = give_unsigned();\n"
      "endmodule\n",
      f, {{"give_unsigned", reinterpret_cast<void*>(&ReturnUnsigned)}},
      "annex_h_06_mismatch");
  EXPECT_TRUE(f.diag.Diagnostics().empty());
}

struct QualifiedPair {
  int x;
  svBitVecVal y;
};

int SumOfPair(const QualifiedPair* pair) {
  return (pair->x * 10) + static_cast<int>(pair->y & 3U);
}

int PairThroughExport() {
  auto sv_pair = NamedExport<int (*)(const QualifiedPair*)>("sv_pair");
  const QualifiedPair kPair = {32, 2U};
  return sv_pair == nullptr ? -1 : sv_pair(&kPair);
}

int TwiceInt(int value) { return 2 * value; }

void AddHundred(int* value) { *value += 100; }

void GiveSeventySeven(int* value) { *value = 77; }

int BitsPlusOne(const svBitVecVal* value) {
  return static_cast<int>(value[0] & 7U) + 1;
}

void GiveSix(svBitVecVal* value) { value[0] = 6U; }

void RunQualified(const std::string& src, SimFixture& f) {
  RunWithImportsBound(
      src, f,
      {{"sum_pair", reinterpret_cast<void*>(&SumOfPair)},
       {"pair_export", reinterpret_cast<void*>(&PairThroughExport)},
       {"twice", reinterpret_cast<void*>(&TwiceInt)},
       {"add_hundred", reinterpret_cast<void*>(&AddHundred)},
       {"give_77", reinterpret_cast<void*>(&GiveSeventySeven)},
       {"bits_plus_one", reinterpret_cast<void*>(&BitsPlusOne)},
       {"give_six", reinterpret_cast<void*>(&GiveSix)}},
      "annex_h_06_qualified");
  EXPECT_TRUE(f.diag.Diagnostics().empty());
}

TEST(DpiRandomQualifiers, AnImportReadsAStructWithRandomMembers) {
  SimFixture f;
  RunQualified(
      "module t;\n"
      "  typedef struct { rand int x; randc bit [1:0] y; } s_t;\n"
      "  import \"DPI-C\" function int sum_pair(input s_t s);\n"
      "  s_t s = '{32, 2};\n"
      "  int r;\n"
      "  initial r = sum_pair(s);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(DesignValue(f, "r"), 322U);
}

TEST(DpiRandomQualifiers, AnExportTakesAStructWithRandomMembers) {
  SimFixture f;
  RunQualified(
      "module t;\n"
      "  typedef struct { rand int x; randc bit [1:0] y; } s_t;\n"
      "  import \"DPI-C\" context function int pair_export();\n"
      "  export \"DPI-C\" function sv_pair;\n"
      "  function int sv_pair(input s_t s); return s.x * 100 + s.y; "
      "endfunction\n"
      "  int r;\n"
      "  initial r = pair_export();\n"
      "endmodule\n",
      f);
  EXPECT_EQ(DesignValue(f, "r"), 3202U);
}

TEST(DpiRandomQualifiers, ARandomPropertyIsReadAsAPlainValue) {
  SimFixture f;
  RunQualified(
      "class C; rand int v; randc bit [2:0] w; endclass\n"
      "module t;\n"
      "  import \"DPI-C\" function int twice(input int v);\n"
      "  import \"DPI-C\" function int bits_plus_one(input bit [2:0] v);\n"
      "  int r, q;\n"
      "  initial begin\n"
      "    automatic C c = new;\n"
      "    c.v = 21;\n"
      "    c.w = 5;\n"
      "    r = twice(c.v);\n"
      "    q = bits_plus_one(c.w);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(DesignValue(f, "r"), 42U);
  EXPECT_EQ(DesignValue(f, "q"), 6U);
}

TEST(DpiRandomQualifiers, ARandPropertyWrittenByAnImportStaysRandom) {
  SimFixture f;
  RunQualified(
      "class C; rand int v; endclass\n"
      "module t;\n"
      "  import \"DPI-C\" function void give_77(output int v);\n"
      "  import \"DPI-C\" function void add_hundred(inout int v);\n"
      "  int out, both, ok, after;\n"
      "  initial begin\n"
      "    automatic C c = new;\n"
      "    give_77(c.v);\n"
      "    out = c.v;\n"
      "    add_hundred(c.v);\n"
      "    both = c.v;\n"
      "    ok = c.randomize() with { v == 5; };\n"
      "    after = c.v;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(DesignValue(f, "out"), 77U);
  EXPECT_EQ(DesignValue(f, "both"), 177U);
  EXPECT_EQ(DesignValue(f, "ok"), 1U);
  EXPECT_EQ(DesignValue(f, "after"), 5U);
}

TEST(DpiRandomQualifiers, ARandcPropertyWrittenByAnImportStaysRandomCyclic) {
  SimFixture f;
  RunQualified(
      "class C; randc bit [2:0] w; endclass\n"
      "module t;\n"
      "  import \"DPI-C\" function void give_six(output bit [2:0] v);\n"
      "  int out;\n"
      "  bit [7:0] seen;\n"
      "  initial begin\n"
      "    automatic C c = new;\n"
      "    give_six(c.w);\n"
      "    out = c.w;\n"
      "    repeat (8) begin\n"
      "      void'(c.randomize());\n"
      "      seen[c.w] = 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(DesignValue(f, "out"), 6U);
  EXPECT_EQ(DesignValue(f, "seen"), 255U);
}

}  // namespace
