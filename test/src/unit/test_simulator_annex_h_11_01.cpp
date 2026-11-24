#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/dpi_runtime.h"
#include "simulator/svdpi.h"

using namespace delta;

namespace {

DpiArg Formal(const char* name, DataTypeKind type, bool is_unsigned,
              uint32_t width = 0) {
  DpiArg formal;
  formal.name = name;
  formal.type = type;
  formal.direction = Direction::kInput;
  formal.is_unsigned = is_unsigned;
  formal.width = width;
  return formal;
}

TEST(DpiTwoStateArguments, TheCHeaderOfF7IsTheExamples) {
  EXPECT_EQ(DpiCFunctionHeader("f7", DataTypeKind::kVoid,
                               {Formal("fbv1", DataTypeKind::kInt, true),
                                Formal("fbv2", DataTypeKind::kInt, true),
                                Formal("fbv3", DataTypeKind::kBit, true, 33)}),
            "void f7(const unsigned int fbv1, const unsigned int fbv2, const "
            "svBitVecVal* fbv3)");
}

TEST(DpiTwoStateArguments, AnArbitraryTwoStateVectorIsCoercedToTheCFormal) {
  EXPECT_EQ(DpiCoercionOfPackedActual(30, 32), DpiActualCoercion::kExtend);
  EXPECT_EQ(DpiCoercionOfPackedActual(32, 32), DpiActualCoercion::kNone);
}

TEST(DpiTwoStateArguments, TheCanonicalTechniqueIsRequiredBeyondSixtyFourBits) {
  EXPECT_TRUE(DpiCCompatibleFormalCanHoldTwoStateVector(33));
  EXPECT_TRUE(DpiCCompatibleFormalCanHoldTwoStateVector(64));
  EXPECT_FALSE(DpiCCompatibleFormalCanHoldTwoStateVector(65));
  EXPECT_EQ(DpiTechniqueRequiredForTwoStateVector(65),
            DpiTwoStateTechnique::kCanonical);
  EXPECT_EQ(DpiTechniqueRequiredForTwoStateVector(33),
            DpiTwoStateTechnique::kCCompatibleFormal);
  EXPECT_TRUE(
      DpiTechniqueIsMoreEfficient(DpiTwoStateTechnique::kCCompatibleFormal,
                                  DpiTwoStateTechnique::kCanonical));
  EXPECT_FALSE(
      DpiTechniqueIsMoreEfficient(DpiTwoStateTechnique::kCanonical,
                                  DpiTwoStateTechnique::kCCompatibleFormal));
}

TEST(DpiTwoStateArguments, F7ReceivesTwoIntsAndACanonicalVector) {
  DpiRuntime rt;
  DpiRtFunction f7;
  f7.sv_name = "f7";
  f7.c_name = "f7";
  f7.return_type = DataTypeKind::kVoid;
  f7.args = {Formal("fbv1", DataTypeKind::kInt, true),
             Formal("fbv2", DataTypeKind::kInt, true),
             Formal("fbv3", DataTypeKind::kBit, true, 33)};
  static uint32_t s_fbv1 = 0;
  static uint32_t s_fbv2 = 0;
  static std::vector<SvLogicVecVal> s_fbv3;
  f7.impl = [](const std::vector<DpiArgValue>& args) -> DpiArgValue {
    s_fbv1 = static_cast<uint32_t>(args[0].AsInt());
    s_fbv2 = static_cast<uint32_t>(args[1].AsInt());
    s_fbv3 = args[2].AsLogicVecWords();
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(f7);

  const DpiArgValue kAbv1 = DpiArgValue::FromInt(-1);
  const DpiArgValue kAbv2 = DpiArgValue::FromInt(0x2ABCDEF0);
  const DpiArgValue kAbv3 = DpiArgValue::FromLogicVecWords(
      {SvLogicVecVal{0x80000001u, 0}, SvLogicVecVal{1u, 0}}, 33,
      DataTypeKind::kBit);
  rt.CallImport("f7", {kAbv1, kAbv2, kAbv3});
  EXPECT_EQ(s_fbv1, 0xFFFFFFFFu);
  EXPECT_EQ(s_fbv2, 0x2ABCDEF0u);
  ASSERT_EQ(s_fbv3.size(), DpiCanonicalWordCount(33));
  EXPECT_EQ(s_fbv3[0].aval, 0x80000001u);
  EXPECT_EQ(s_fbv3[1].aval, 1u);
}

void SeeTwoWordsAndAVector(unsigned int fbv1, unsigned int fbv2,
                           const svBitVecVal* fbv3) {
  SeeInC({fbv1, fbv2, fbv3[0], SV_GET_UNSIGNED_BITS(fbv3[1], 1)});
}

void RunExampleFour(SimFixture& f, const std::string& range,
                    const char* dir_name) {
  RunModuleWithC(
      "  parameter W = 33;\n"
      "  localparam L = 32;\n"
      "  int abv1;\n"
      "  bit [29:0] abv2;\n"
      "  bit [W-1:0] abv3;\n"
      "  import \"DPI-C\" function void f7(input int unsigned fbv1,\n"
      "      input int unsigned fbv2, input bit " +
          range +
          " fbv3);\n"
          "  initial begin\n"
          "    abv1 = 32'h8123_4567;\n"
          "    abv2 = 30'h2abc_def0;\n"
          "    abv3 = 33'h1_0000_0005;\n"
          "    f7(abv1, abv2, abv3);\n"
          "  end\n",
      f, {{"f7", CAddress(&SeeTwoWordsAndAVector)}}, dir_name);
}

TEST(DpiTwoStateArguments, ADesignsVectorsAreCoercedToTheCFormals) {
  SimFixture f;
  RunExampleFour(f, "[32:0]", "annex_h_11_01_literal");
  EXPECT_EQ(SeenInC(), (std::vector<long long>{0x81234567, 0x2ABCDEF0, 5, 1}));
}

TEST(DpiTwoStateArguments, DISABLED_AFormalTakesItsWidthFromAParameter) {
  SimFixture f;
  RunExampleFour(f, "[W-1:0]", "annex_h_11_01_parameter");
  EXPECT_EQ(SeenInC(), (std::vector<long long>{0x81234567, 0x2ABCDEF0, 5, 1}));
}

TEST(DpiTwoStateArguments, DISABLED_AFormalTakesItsWidthFromALocalParameter) {
  SimFixture f;
  RunExampleFour(f, "[L:0]", "annex_h_11_01_localparam");
  EXPECT_EQ(SeenInC(), (std::vector<long long>{0x81234567, 0x2ABCDEF0, 5, 1}));
}

void SeeFiveElements(const int a[5]) { SeeInC({a[0], a[4]}); }

TEST(DpiTwoStateArguments, AnUnpackedFormalTakesItsSizeFromAParameter) {
  SimFixture f;
  RunModuleWithC(
      "  parameter N = 5;\n"
      "  int v [N];\n"
      "  import \"DPI-C\" function void see(input int a [N]);\n"
      "  initial begin\n"
      "    foreach (v[i]) v[i] = i + 10;\n"
      "    see(v);\n"
      "  end\n",
      f, {{"see", CAddress(&SeeFiveElements)}}, "annex_h_11_01_unpacked");
  EXPECT_EQ(SeenInC(), (std::vector<long long>{10, 14}));
}

void SeeFourSizes(unsigned char b, unsigned short s, unsigned long long l) {
  SeeInC({b, s, static_cast<long long>(l)});
}

TEST(DpiTwoStateArguments, AVectorOfAnyWidthBindsToEachCCompatibleFormal) {
  SimFixture f;
  RunModuleWithC(
      "  import \"DPI-C\" function void sizes(input byte unsigned b,\n"
      "      input shortint unsigned s, input longint unsigned l);\n"
      "  bit [4:0] narrow = 5'h1f;\n"
      "  bit [19:0] wide = 20'hf8001;\n"
      "  bit [49:0] wider = 50'h2_0000_0000_0003;\n"
      "  initial sizes(narrow, wide, wider);\n",
      f, {{"sizes", CAddress(&SeeFourSizes)}}, "annex_h_11_01_sizes");
  EXPECT_EQ(SeenInC(),
            (std::vector<long long>{0x1F, 0x8001, 0x2000000000003LL}));
}

}  // namespace
