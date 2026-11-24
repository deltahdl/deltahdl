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

DpiArg Formal(DataTypeKind type, Direction direction, bool is_unsigned,
              uint32_t width = 0) {
  DpiArg formal;
  formal.name = "a";
  formal.type = type;
  formal.direction = direction;
  formal.is_unsigned = is_unsigned;
  formal.width = width;
  return formal;
}

TEST(DpiBasicTypes, EachBasicTypeMapsToItsCType) {
  EXPECT_EQ(DpiCTypeOfBasicType(DataTypeKind::kByte, false), "char");
  EXPECT_EQ(DpiCTypeOfBasicType(DataTypeKind::kShortint, false), "short int");
  EXPECT_EQ(DpiCTypeOfBasicType(DataTypeKind::kInt, false), "int");
  EXPECT_EQ(DpiCTypeOfBasicType(DataTypeKind::kLongint, false), "long long");
  EXPECT_EQ(DpiCTypeOfBasicType(DataTypeKind::kReal, false), "double");
  EXPECT_EQ(DpiCTypeOfBasicType(DataTypeKind::kShortreal, false), "float");
  EXPECT_EQ(DpiCTypeOfBasicType(DataTypeKind::kChandle, false), "void*");
  EXPECT_EQ(DpiCTypeOfBasicType(DataTypeKind::kString, false), "const char*");
  EXPECT_EQ(DpiCTypeOfBasicType(DataTypeKind::kBit, false), "unsigned char");
  EXPECT_EQ(DpiCTypeOfBasicType(DataTypeKind::kLogic, false), "unsigned char");
  EXPECT_EQ(DpiCTypeOfBasicType(DataTypeKind::kReg, false), "unsigned char");
  EXPECT_EQ(DpiCTypeOfBasicType(DataTypeKind::kStruct, false), "");
  EXPECT_EQ(DpiCTypeOfBasicType(DataTypeKind::kEvent, false), "");
}

TEST(DpiBasicTypes, TheUnsignedIntegerTypesMapToTheUnsignedCTypes) {
  EXPECT_EQ(DpiCTypeOfBasicType(DataTypeKind::kByte, true), "unsigned char");
  EXPECT_EQ(DpiCTypeOfBasicType(DataTypeKind::kShortint, true),
            "unsigned short");
  EXPECT_EQ(DpiCTypeOfBasicType(DataTypeKind::kInt, true), "unsigned int");
  EXPECT_EQ(DpiCTypeOfBasicType(DataTypeKind::kLongint, true),
            "unsigned long long");
  EXPECT_EQ(DpiCTypeOfBasicType(DataTypeKind::kReal, true), "double");
  EXPECT_EQ(DpiCTypeOfBasicType(DataTypeKind::kBit, true), "unsigned char");
  EXPECT_EQ(DpiCTypeOfBasicType(DataTypeKind::kString, true), "const char*");
}

TEST(DpiBasicTypes, AnUnsignedByteInputIsNotABitVectorOfEight) {
  EXPECT_EQ(DpiCTypeOfFormal(
                Formal(DataTypeKind::kByte, Direction::kInput, true), false),
            "const unsigned char");
  EXPECT_EQ(DpiCTypeOfFormal(
                Formal(DataTypeKind::kBit, Direction::kInput, false, 8), false),
            "const svBitVecVal*");
  EXPECT_EQ(
      DpiCTypeOfFormal(Formal(DataTypeKind::kShortint, Direction::kInput, true),
                       false),
      "const unsigned short");
  EXPECT_EQ(
      DpiCTypeOfFormal(Formal(DataTypeKind::kBit, Direction::kInput, false, 16),
                       false),
      "const svBitVecVal*");
  EXPECT_EQ(DpiCTypeOfFormal(
                Formal(DataTypeKind::kByte, Direction::kInput, false), false),
            "const char");
}

TEST(DpiBasicTypes, AnUnsignedByteOutputIsNotABitVectorOfEight) {
  EXPECT_EQ(DpiCTypeOfFormal(
                Formal(DataTypeKind::kByte, Direction::kOutput, true), false),
            "unsigned char*");
  EXPECT_EQ(
      DpiCTypeOfFormal(Formal(DataTypeKind::kBit, Direction::kOutput, false, 8),
                       false),
      "svBitVecVal*");
  EXPECT_EQ(DpiCTypeOfFormal(
                Formal(DataTypeKind::kLongint, Direction::kInout, true), false),
            "unsigned long long*");
  EXPECT_EQ(DpiCTypeOfFormal(
                Formal(DataTypeKind::kInt, Direction::kInout, true), false),
            "unsigned int*");
}

void SeeVector(const svBitVecVal* v) { SeeInC({v[0] & 0xFFFFU}); }

void WriteByteAndVector(unsigned char* u, svBitVecVal* b) {
  *u = 200;
  *b = 0xFFFFFF37U;
}

void AddToByteAndVector(unsigned char* u, svBitVecVal* b) {
  SeeInC({*u, *b & 0xFFU});
  *u = static_cast<unsigned char>(*u + 100);
  *b = (*b & 0xFFU) + 0x100U + 100U;
}

void WriteShortAndVector(unsigned short* u, svBitVecVal* b) {
  *u = 60000;
  *b = 0xFFFF1234U;
}

void AddToShortAndVector(unsigned short* u, svBitVecVal* b) {
  SeeInC({*u, *b & 0xFFFFU});
  *u = static_cast<unsigned short>(*u + 20000);
  *b = (*b & 0xFFFFU) + 0x10000U + 20000U;
}

void WriteUnsigned(unsigned* i, unsigned long long* l) {
  *i = 4294967295U;
  *l = 0xFFFFFFFFFFFFFFF0ULL;
}

void AddToUnsigned(unsigned* i, unsigned long long* l) {
  *i += 5U;
  *l += 5ULL;
}

unsigned long long PlusOne(unsigned long long v) { return v + 1; }

void RunUnsigned(const std::string& items, SimFixture& f) {
  RunModuleWithC(items, f,
                 {{"see_vector", CAddress(&SeeVector)},
                  {"write_byte", CAddress(&WriteByteAndVector)},
                  {"add_byte", CAddress(&AddToByteAndVector)},
                  {"write_short", CAddress(&WriteShortAndVector)},
                  {"add_short", CAddress(&AddToShortAndVector)},
                  {"write_unsigned", CAddress(&WriteUnsigned)},
                  {"add_unsigned", CAddress(&AddToUnsigned)},
                  {"plus_one", CAddress(&PlusOne)}},
                 "annex_h_07_04_unsigned");
}

TEST(DpiUnsignedTypes, ABitVectorOfTheirWidthIsPassedByReference) {
  SimFixture f;
  RunUnsigned(
      "  import \"DPI-C\" function void see_vector(input bit [15:0] v);\n"
      "  initial see_vector(16'd60000);\n",
      f);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{60000}));
}

TEST(DpiUnsignedTypes, AByteWideBitVectorIsPassedByReference) {
  SimFixture f;
  RunUnsigned(
      "  import \"DPI-C\" function void see_vector(input bit [7:0] v);\n"
      "  initial see_vector(8'd200);\n",
      f);
  ASSERT_EQ(SeenInC().size(), 1U);
  EXPECT_EQ(SeenInC()[0] & 0xFF, 200);
}

TEST(DpiUnsignedTypes, AnUnsignedByteAndABitVectorAreWrittenByTheirPointers) {
  SimFixture f;
  RunUnsigned(
      "  import \"DPI-C\" function void write_byte(output byte unsigned u,\n"
      "      output bit [7:0] b);\n"
      "  import \"DPI-C\" function void add_byte(inout byte unsigned u,\n"
      "      inout bit [7:0] b);\n"
      "  byte unsigned u;\n"
      "  bit [7:0] b;\n"
      "  int wu, wb, au, ab;\n"
      "  initial begin\n"
      "    write_byte(u, b); wu = u; wb = b;\n"
      "    u = 130; b = 150; add_byte(u, b); au = u; ab = b;\n"
      "  end\n",
      f);
  EXPECT_EQ(DesignValue(f, "wu"), 200U);
  EXPECT_EQ(DesignValue(f, "wb"), 0x37U);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{130, 150}));
  EXPECT_EQ(DesignValue(f, "au"), 230U);
  EXPECT_EQ(DesignValue(f, "ab"), 250U);
}

TEST(DpiUnsignedTypes, AnUnsignedShortAndABitVectorAreWrittenByTheirPointers) {
  SimFixture f;
  RunUnsigned(
      "  import \"DPI-C\" function void write_short(\n"
      "      output shortint unsigned u, output bit [15:0] b);\n"
      "  import \"DPI-C\" function void add_short(\n"
      "      inout shortint unsigned u, inout bit [15:0] b);\n"
      "  shortint unsigned u;\n"
      "  bit [15:0] b;\n"
      "  int wu, wb, au, ab;\n"
      "  initial begin\n"
      "    write_short(u, b); wu = u; wb = b;\n"
      "    u = 40000; b = 45000; add_short(u, b); au = u; ab = b;\n"
      "  end\n",
      f);
  EXPECT_EQ(DesignValue(f, "wu"), 60000U);
  EXPECT_EQ(DesignValue(f, "wb"), 0x1234U);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{40000, 45000}));
  EXPECT_EQ(DesignValue(f, "au"), 60000U);
  EXPECT_EQ(DesignValue(f, "ab"), 65000U);
}

TEST(DpiUnsignedTypes, AnUnsignedLongintKeepsItsTopBit) {
  SimFixture f;
  RunUnsigned(
      "  import \"DPI-C\" function longint unsigned plus_one(\n"
      "      input longint unsigned v);\n"
      "  bit exact, positive;\n"
      "  initial begin\n"
      "    exact = plus_one(64'hffff_ffff_ffff_fff0) ==\n"
      "        64'hffff_ffff_ffff_fff1;\n"
      "    positive = plus_one(64'hffff_ffff_ffff_fff0) > 0;\n"
      "  end\n",
      f);
  EXPECT_EQ(DesignValue(f, "exact"), 1U);
  EXPECT_EQ(DesignValue(f, "positive"), 1U);
}

TEST(DpiUnsignedTypes, WiderOnesAreWrittenWithTheirWholeRange) {
  SimFixture f;
  RunUnsigned(
      "  import \"DPI-C\" function void write_unsigned(\n"
      "      output int unsigned i, output longint unsigned l);\n"
      "  import \"DPI-C\" function void add_unsigned(\n"
      "      inout int unsigned i, inout longint unsigned l);\n"
      "  int unsigned i;\n"
      "  longint unsigned l;\n"
      "  longint wide;\n"
      "  bit above;\n"
      "  int unsigned i2 = 32'd4294967280;\n"
      "  longint unsigned l2 = 64'hffff_ffff_ffff_fff0;\n"
      "  initial begin\n"
      "    write_unsigned(i, l);\n"
      "    wide = i;\n"
      "    above = l > 64'h8000_0000_0000_0000;\n"
      "    add_unsigned(i2, l2);\n"
      "  end\n",
      f);
  EXPECT_EQ(DesignValue(f, "wide"), 4294967295U);
  EXPECT_EQ(DesignValue(f, "l"), 0xFFFFFFFFFFFFFFF0U);
  EXPECT_EQ(DesignValue(f, "above"), 1U);
  EXPECT_EQ(DesignValue(f, "i2"), 4294967285U);
  EXPECT_EQ(DesignValue(f, "l2"), 0xFFFFFFFFFFFFFFF5U);
}

void SeeLogicChunk(const svLogicVecVal* v) { SeeInC({v->aval, v->bval}); }

void SeeWideBits(const svBitVecVal* v) { SeeInC({v[0], v[1] & 0xFFU}); }

void SeeWideLogic(const svLogicVecVal* v) {
  SeeInC({v[0].aval, v[0].bval, v[1].aval & 0xFFU, v[1].bval & 0xFFU});
}

void SeeFiveBits(const svBitVecVal* v) { SeeInC({v[0] & 31U}); }

void SeeFiveLogics(const svLogicVecVal* v) {
  SeeInC({v->aval & 31U, v->bval & 31U});
}

void WriteBits(svBitVecVal* v) { v[0] = 0xA5U; }

void AddToBits(svBitVecVal* v) { v[0] = (v[0] & 0xFFU) + 0x11U; }

void WriteLogics(svLogicVecVal* v) { *v = {0xACU, 0x05U}; }

void CallWithAggregates() {
  auto take = NamedExport<void (*)(const svBitVecVal*, svLogicVecVal*)>(
      "sv_take_aggregates");
  if (take == nullptr) return;
  const svBitVecVal kIn = 0xA5U;
  svLogicVecVal out = {0U, 0U};
  take(&kIn, &out);
  SeeInC({out.aval & 0xFFU, out.bval & 0xFFU});
}

void RunAggregates(const std::string& items, SimFixture& f) {
  RunModuleWithC(items, f,
                 {{"see_logic", CAddress(&SeeLogicChunk)},
                  {"see_wide", CAddress(&SeeWideBits)},
                  {"see_wide_logic", CAddress(&SeeWideLogic)},
                  {"see_five", CAddress(&SeeFiveBits)},
                  {"see_five_logic", CAddress(&SeeFiveLogics)},
                  {"write_bits", CAddress(&WriteBits)},
                  {"add_bits", CAddress(&AddToBits)},
                  {"write_logics", CAddress(&WriteLogics)},
                  {"call_export", CAddress(&CallWithAggregates)}},
                 "annex_h_07_04_aggregates");
}

TEST(DpiPackedAggregatesInADesign, AFourStateStructKeepsItsUnknownBits) {
  SimFixture f;
  RunAggregates(
      "  typedef struct packed { logic [3:0] h; logic [3:0] p; } s_t;\n"
      "  import \"DPI-C\" function void see_logic(input s_t s);\n"
      "  s_t s;\n"
      "  initial begin s.h = 4'h2; s.p = 4'b1x0z; see_logic(s); end\n",
      f);
  ASSERT_EQ(SeenInC().size(), 2U);
  EXPECT_EQ(SeenInC()[0] & 0xFF, 0x2C);
  EXPECT_EQ(SeenInC()[1] & 0xFF, 0x05);
}

TEST(DpiPackedAggregatesInADesign, AWideOneCrossesLeastSignificantChunkFirst) {
  SimFixture f;
  RunAggregates(
      "  typedef struct packed { bit [7:0] top; bit [31:0] low; } s_t;\n"
      "  typedef struct packed { logic [7:0] top; logic [31:0] low; } l_t;\n"
      "  import \"DPI-C\" function void see_wide(input s_t s);\n"
      "  import \"DPI-C\" function void see_wide_logic(input l_t s);\n"
      "  s_t s = '{8'hab, 32'h1234_5678};\n"
      "  l_t l = '{8'hzb, 32'h1234_567x};\n"
      "  initial begin see_wide(s); see_wide_logic(l); end\n",
      f);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{0x12345678, 0xAB, 0x1234567F,
                                               0xF, 0x0B, 0xF0}));
}

TEST(DpiPackedAggregatesInADesign, AWideUnionCrossesAsItsVector) {
  SimFixture f;
  RunAggregates(
      "  typedef union packed { bit [39:0] a; bit [4:0][7:0] b; } u_t;\n"
      "  import \"DPI-C\" function void see_wide(input u_t u);\n"
      "  u_t u;\n"
      "  initial begin\n"
      "    u.a = 40'hcd_1234_5678; see_wide(u);\n"
      "  end\n",
      f);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{0x12345678, 0xCD}));
}

TEST(DpiPackedAggregatesInADesign, DISABLED_ATaggedUnionHasItsTagInTheTopBits) {
  SimFixture f;
  RunAggregates(
      "  typedef union tagged packed { bit [3:0] X; bit [3:0] Y; } u_t;\n"
      "  import \"DPI-C\" function void see_five(input u_t u);\n"
      "  u_t u;\n"
      "  initial begin\n"
      "    u = tagged Y 4'h5; see_five(u);\n"
      "    u = tagged X 4'h6; see_five(u);\n"
      "  end\n",
      f);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{21, 6}));
}

TEST(DpiPackedAggregatesInADesign,
     DISABLED_AFourStateTaggedUnionsTagIsTwoState) {
  SimFixture f;
  RunAggregates(
      "  typedef union tagged packed { logic [3:0] X; logic [3:0] Y; } u_t;\n"
      "  import \"DPI-C\" function void see_five_logic(input u_t u);\n"
      "  u_t u;\n"
      "  initial begin u = tagged Y 4'b1x0z; see_five_logic(u); end\n",
      f);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{0x1C, 0x05}));
}

TEST(DpiPackedAggregatesInADesign, AnOutputOrAnInoutIsCopiedBackToItsMembers) {
  SimFixture f;
  RunAggregates(
      "  typedef struct packed { bit [3:0] h; bit [3:0] l; } s_t;\n"
      "  typedef union packed { bit [7:0] a; bit [1:0][3:0] b; } u_t;\n"
      "  typedef struct packed { logic [3:0] h; logic [3:0] l; } l_t;\n"
      "  import \"DPI-C\" function void write_bits(output s_t s);\n"
      "  import \"DPI-C\" function void add_bits(inout u_t u);\n"
      "  import \"DPI-C\" function void write_logics(output l_t s);\n"
      "  s_t s;\n"
      "  u_t u;\n"
      "  l_t l;\n"
      "  int sh, sl, uh, ul;\n"
      "  bit lh, ll;\n"
      "  initial begin\n"
      "    write_bits(s); sh = s.h; sl = s.l;\n"
      "    u.a = 8'h73; add_bits(u); uh = u.b[1]; ul = u.b[0];\n"
      "    write_logics(l); lh = l.h === 4'ha; ll = l.l === 4'b1x0z;\n"
      "  end\n",
      f);
  EXPECT_EQ(DesignValue(f, "sh"), 0xAU);
  EXPECT_EQ(DesignValue(f, "sl"), 0x5U);
  EXPECT_EQ(DesignValue(f, "uh"), 0x8U);
  EXPECT_EQ(DesignValue(f, "ul"), 0x4U);
  EXPECT_EQ(DesignValue(f, "lh"), 1U);
  EXPECT_EQ(DesignValue(f, "ll"), 1U);
}

TEST(DpiPackedAggregatesInADesign, AnExportTakesThemInCanonicalForm) {
  SimFixture f;
  RunAggregates(
      "  typedef union packed { bit [7:0] a; bit [1:0][3:0] b; } u_t;\n"
      "  typedef struct packed { logic [3:0] h; logic [3:0] l; } l_t;\n"
      "  import \"DPI-C\" context function void call_export();\n"
      "  export \"DPI-C\" function sv_take_aggregates;\n"
      "  int high, low;\n"
      "  function void sv_take_aggregates(input u_t u, output l_t s);\n"
      "    high = u.b[1]; low = u.b[0];\n"
      "    s.h = 4'h9; s.l = 4'b1x0z;\n"
      "  endfunction\n"
      "  initial call_export();\n",
      f);
  EXPECT_EQ(DesignValue(f, "high"), 0xAU);
  EXPECT_EQ(DesignValue(f, "low"), 0x5U);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{0x9C, 0x05}));
}

void SeeScalar(svLogic v) { SeeInC({v}); }

void WriteScalars(svLogic* x, svLogic* z) {
  *x = sv_x;
  *z = sv_z;
}

TEST(DpiScalarEncodings, AScalarHoldingZReachesCAsItsCode) {
  SimFixture f;
  RunModuleWithC(
      "  import \"DPI-C\" function void see_logic(input logic v);\n"
      "  import \"DPI-C\" function void see_reg(input reg v);\n"
      "  initial begin\n"
      "    see_logic(1'bz); see_reg(1'bz); see_logic(1'bx); see_reg(1'b1);\n"
      "  end\n",
      f,
      {{"see_logic", CAddress(&SeeScalar)}, {"see_reg", CAddress(&SeeScalar)}},
      "annex_h_07_04_scalar_inputs");
  EXPECT_EQ(SeenInC(), (std::vector<long long>{sv_z, sv_z, sv_x, sv_1}));
}

TEST(DpiScalarEncodings, AnUnknownWrittenInCIsReadBackInTheDesign) {
  SimFixture f;
  RunModuleWithC(
      "  import \"DPI-C\" function void write_scalars(output logic x,\n"
      "      output reg z);\n"
      "  logic x;\n"
      "  reg z;\n"
      "  bit x_ok, z_ok;\n"
      "  initial begin\n"
      "    x = 1'b0; z = 1'b0;\n"
      "    write_scalars(x, z);\n"
      "    x_ok = x === 1'bx; z_ok = z === 1'bz;\n"
      "  end\n",
      f, {{"write_scalars", CAddress(&WriteScalars)}},
      "annex_h_07_04_scalar_outputs");
  EXPECT_EQ(DesignValue(f, "x_ok"), 1U);
  EXPECT_EQ(DesignValue(f, "z_ok"), 1U);
}

}  // namespace
