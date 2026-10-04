#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/dpi_runtime.h"

using namespace delta;

// Annex H.8.4 (Argument passing by reference): an argument passed by
// reference is passed as a pointer to the actual data object, and for
// packed data as a pointer to a canonical data object; an argument of type
// T passed by reference has a formal of type T*, a packed array a pointer
// to the canonical type, svLogicVecVal* or svBitVecVal*; and a DPI C
// application shall make no assumption about the lifetime of an argument
// passed by reference, so a value to keep across calls is copied into
// memory the C application owns and manages. The cases check what the
// pointer refers to and its type for each kind of formal, and that the
// reference is not to be kept.

namespace {

DpiArg Formal(DataTypeKind type, Direction direction, uint32_t width = 0) {
  DpiArg formal;
  formal.name = "a";
  formal.type = type;
  formal.direction = direction;
  formal.width = width;
  return formal;
}

// §H.8.4: a T passed by reference is a T* -- int*, double*, void** for a
// chandle, const char** for a string -- and packed data a pointer to its
// canonical object, svBitVecVal* or svLogicVecVal*, const for an input.
TEST(DpiPassingByReference, AReferenceIsAPointerToTheTypeOrItsCanonicalForm) {
  EXPECT_EQ(DpiReferentOfFormal(Formal(DataTypeKind::kInt, Direction::kOutput)),
            DpiReferent::kActualDataObject);
  EXPECT_EQ(
      DpiCTypeOfFormal(Formal(DataTypeKind::kInt, Direction::kOutput), false),
      "int*");
  EXPECT_EQ(
      DpiCTypeOfFormal(Formal(DataTypeKind::kReal, Direction::kInout), false),
      "double*");
  EXPECT_EQ(DpiCTypeOfFormal(Formal(DataTypeKind::kChandle, Direction::kInout),
                             false),
            "void**");
  EXPECT_EQ(DpiCTypeOfFormal(Formal(DataTypeKind::kString, Direction::kOutput),
                             false),
            "const char**");
  EXPECT_EQ(
      DpiReferentOfFormal(Formal(DataTypeKind::kBit, Direction::kOutput, 8)),
      DpiReferent::kCanonicalDataObject);
  EXPECT_EQ(DpiCTypeOfFormal(Formal(DataTypeKind::kBit, Direction::kOutput, 8),
                             false),
            "svBitVecVal*");
  EXPECT_EQ(DpiCTypeOfFormal(
                Formal(DataTypeKind::kLogic, Direction::kInout, 40), false),
            "svLogicVecVal*");
  EXPECT_EQ(
      DpiReferentOfFormal(Formal(DataTypeKind::kLogic, Direction::kInput, 40)),
      DpiReferent::kCanonicalDataObject);
  EXPECT_EQ(DpiCTypeOfFormal(
                Formal(DataTypeKind::kLogic, Direction::kInput, 40), false),
            "const svLogicVecVal*");
  EXPECT_EQ(
      DpiReferentOfFormal(Formal(DataTypeKind::kInteger, Direction::kInput)),
      DpiReferent::kCanonicalDataObject);
}

// §H.8.4: no assumption holds about the lifetime of a reference beyond the
// call, and a value kept across calls lives in memory the C application
// owns.
TEST(DpiPassingByReference, AReferenceIsNotToBeKeptAcrossCalls) {
  EXPECT_FALSE(DpiReferenceOutlivesTheCall());
  EXPECT_EQ(DpiSideOwningACopyKeptAcrossCalls(), DpiMemorySide::kC);
}

// The C functions the imports below are bound to, each reading a packed input
// through the pointer to its canonical representation.
int TopWordByReference(const uint32_t* v) { return static_cast<int>(v[3]); }

long long UpperPairByReference(const SvLogicVecVal* v) {
  return (static_cast<long long>(v[1].aval) * 1000) + v[1].bval;
}

int IntegerAndTimeByReference(const SvLogicVecVal* integer,
                              const SvLogicVecVal* time) {
  return static_cast<int>((integer[0].aval * 1000) + (integer[0].bval * 100) +
                          (time[1].aval * 10) + time[0].aval);
}

// §H.8.4: a packed input is passed by reference to its canonical
// representation, 32 bits to a chunk with the least significant chunk first
// (§H.7.7) -- svBitVecVal words for a 2-state array, svLogicVecVal pairs for a
// 4-state one, whose bval keeps an unknown bit unknown.
TEST(DpiPassingByReference, APackedInputArrivesAsItsCanonicalArray) {
  DpiCBinding b;
  b.dpi.RegisterImport(
      CImport("top_word", DataTypeKind::kInt,
              {CFormal("v", DataTypeKind::kBit, Direction::kInput, 128)}));
  b.dpi.RegisterImport(
      CImport("upper_pair", DataTypeKind::kLongint,
              {CFormal("v", DataTypeKind::kLogic, Direction::kInput, 40)}));
  b.Bind({{"top_word", reinterpret_cast<void*>(&TopWordByReference)},
          {"upper_pair", reinterpret_cast<void*>(&UpperPairByReference)}},
         "annex_h_08_04_packed");
  ASSERT_TRUE(b.diag.Diagnostics().empty());
  std::vector<DpiArgValue> wide = {DpiArgValue::FromLogicVecWords(
      {{1, 0}, {2, 0}, {3, 0}, {0x12345678, 0}}, 128, DataTypeKind::kBit)};
  EXPECT_EQ(b.Call("top_word", wide).AsInt(), 0x12345678);
  // Bit 33 of the logic array is x: aval and bval both set, in the second
  // chunk.
  std::vector<DpiArgValue> logic = {DpiArgValue::FromLogicVecWords(
      {{0, 0}, {3, 2}}, 40, DataTypeKind::kLogic)};
  EXPECT_EQ(b.Call("upper_pair", logic).AsLongint(), 3002);
}

// §H.7.3: integer and time are packed 4-state types, an integer one chunk and
// a time two, so they too cross by reference to svLogicVecVal pairs.
TEST(DpiPassingByReference, IntegerAndTimeArriveAsCanonicalPairs) {
  DpiCBinding b;
  b.dpi.RegisterImport(
      CImport("integer_and_time", DataTypeKind::kInt,
              {CFormal("i", DataTypeKind::kInteger, Direction::kInput),
               CFormal("t", DataTypeKind::kTime, Direction::kInput)}));
  b.Bind({{"integer_and_time",
           reinterpret_cast<void*>(&IntegerAndTimeByReference)}},
         "annex_h_08_04_integer_time");
  ASSERT_TRUE(b.diag.Diagnostics().empty());
  DpiArgValue time = DpiArgValue::FromLongint((2LL << 32) | 5);
  time.type = DataTypeKind::kTime;
  std::vector<DpiArgValue> args = {DpiArgValue::FromLogicVec({4, 1}), time};
  EXPECT_EQ(b.Call("integer_and_time", args).AsInt(), 4125);
}

// The C functions the design below calls: one reading a one-bit packed array
// of each kind through the pointer to its canonical chunk, one writing a
// one-bit packed output there, one reading a time's two chunks and one
// writing unknown bits into a time output.
int OneBitArrays(const uint32_t* bits, const SvLogicVecVal* logic) {
  return static_cast<int>((bits[0] * 100) + (logic[0].aval * 10) +
                          logic[0].bval);
}

void OneBitArrayOut(uint32_t* bits) { bits[0] = 1; }

int TimeChunks(const SvLogicVecVal* time) {
  return static_cast<int>((time[0].aval * 100) + time[0].bval +
                          (time[1].aval * 10000));
}

void TimeWithUnknownBits(SvLogicVecVal* time) {
  time[0] = {5, 4};
  time[1] = {0, 0};
}

// The value the design's variable `name` holds once the run is over, all ones
// where the run holds no such variable.
uint64_t VariableValue(SimFixture& f, std::string_view name) {
  auto* var = f.ctx.FindVariable(name);
  return var == nullptr ? ~uint64_t{0} : var->value.ToUint64();
}

// The design binding the four imports above, run to its end.
void RunOneBitAndTimeDesign(SimFixture& f) {
  RunWithImportsBound(
      "module t;\n"
      "  import \"DPI-C\" function int one_bit_arrays(input bit [0:0] b,\n"
      "                                               input logic [0:0] l);\n"
      "  import \"DPI-C\" function void one_bit_out(output bit [0:0] o);\n"
      "  import \"DPI-C\" function int time_chunks(input time t);\n"
      "  import \"DPI-C\" function void time_out(output time t);\n"
      "  int ones, chunks;\n"
      "  bit [0:0] o;\n"
      "  time t_in, t_out;\n"
      "  bit unknown, low;\n"
      "  initial begin\n"
      "    ones = one_bit_arrays(1'b1, 1'bx);\n"
      "    one_bit_out(o);\n"
      "    t_in = 64'b1x0z;\n"
      "    chunks = time_chunks(t_in);\n"
      "    time_out(t_out);\n"
      "    unknown = t_out[2] === 1'bx;\n"
      "    low = t_out[0];\n"
      "  end\n"
      "endmodule\n",
      f,
      {{"one_bit_arrays", reinterpret_cast<void*>(&OneBitArrays)},
       {"one_bit_out", reinterpret_cast<void*>(&OneBitArrayOut)},
       {"time_chunks", reinterpret_cast<void*>(&TimeChunks)},
       {"time_out", reinterpret_cast<void*>(&TimeWithUnknownBits)}},
      "annex_h_08_04_one_bit_and_time");
}

// §H.8.4 with §H.7.3: a one-bit packed array is still a packed array, so it
// crosses by reference to one canonical chunk rather than by value as the
// scalar of its kind -- the x of the logic one arriving with aval and bval
// both set.
TEST(DpiPassingByReference, AOneBitPackedArrayCrossesAsItsCanonicalChunk) {
  SimFixture f;
  RunOneBitAndTimeDesign(f);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(VariableValue(f, "ones"), 111U);
}

// And a one-bit packed output is written through that chunk.
TEST(DpiPassingByReference, AOneBitPackedOutputIsWrittenThroughItsChunk) {
  SimFixture f;
  RunOneBitAndTimeDesign(f);
  EXPECT_EQ(VariableValue(f, "o"), 1U);
}

// §H.7.3: time is a packed 4-state type, so its x and z bits reach C as the
// bval of its chunks rather than being cleared: 64'b1x0z is aval 1100 and
// bval 0101.
TEST(DpiPassingByReference, ATimeKeepsItsUnknownBitsOnTheWayToC) {
  SimFixture f;
  RunOneBitAndTimeDesign(f);
  EXPECT_EQ(VariableValue(f, "chunks"), 1205U);
}

// And the unknown bits C writes into a time output come back unknown.
TEST(DpiPassingByReference, ATimeOutputKeepsTheUnknownBitsCWrote) {
  SimFixture f;
  RunOneBitAndTimeDesign(f);
  EXPECT_EQ(VariableValue(f, "unknown"), 1U);
  EXPECT_EQ(VariableValue(f, "low"), 1U);
}
}  // namespace
