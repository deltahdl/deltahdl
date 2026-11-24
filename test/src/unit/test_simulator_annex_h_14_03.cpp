#include <gtest/gtest.h>

#include <cstddef>
#include <filesystem>
#include <fstream>
#include <sstream>
#include <string>
#include <type_traits>
#include <vector>

#include "simulator/dpi_runtime.h"
#include "simulator/svdpi.h"
#include "simulator/svdpi_src.h"
#include "simulator/svdpi_sv31a.h"

using namespace delta;

namespace {

TEST(SvdpiSrcIncludeFile, TwoSymbolsDecideBinaryOrSourceCompatibility) {
  EXPECT_EQ(DpiSvdpiSrcSymbolCount(), 2u);
  EXPECT_EQ(DpiCompatibilityOfApplication(false),
            DpiApplicationCompatibility::kBinary);
  EXPECT_EQ(DpiCompatibilityOfApplication(true),
            DpiApplicationCompatibility::kSource);
  EXPECT_FALSE(DpiApplicationIsRecompiledPerSimulator(false));
  EXPECT_TRUE(DpiApplicationIsRecompiledPerSimulator(true));
}

TEST(SvdpiSrcIncludeFile, TheMacrosDeclareNoArrayType) {
  EXPECT_FALSE(DpiPackedArrayMacroMayDefineAnArrayType());
  SV_BIT_PACKED_ARRAY(40, bits);
  SV_LOGIC_PACKED_ARRAY(64, logic);
  EXPECT_FALSE(std::is_array<decltype(bits)>::value);
  EXPECT_FALSE(std::is_array<decltype(logic)>::value);
  EXPECT_EQ(sizeof(bits), static_cast<size_t>(svSizeOfBitPackedArr(40)));
  EXPECT_EQ(sizeof(logic), static_cast<size_t>(svSizeOfLogicPackedArr(64)));
}

TEST(SvdpiSrcIncludeFile, ADeclaredVariableIsAPackedArrayReference) {
  SV_BIT_PACKED_ARRAY(40, bits);
  const svBitVec32 kIn[2] = {0x00000005u, 0x80u};
  svPutBitVec32(&bits, kIn, 40);
  EXPECT_EQ(svGetSelectBit(&bits, 0), sv_1);
  EXPECT_EQ(svGetSelectBit(&bits, 1), sv_0);
  EXPECT_EQ(svGetSelectBit(&bits, 2), sv_1);
  EXPECT_EQ(svGetSelectBit(&bits, 39), sv_1);

  SV_LOGIC_PACKED_ARRAY(8, logic);
  const svLogicVec32 kZ = {0x0u, 0x1u};
  svPutLogicVec32(&logic, &kZ, 8);
  EXPECT_EQ(svGetSelectLogic(&logic, 0), sv_z);
  EXPECT_EQ(svGetSelectLogic(&logic, 1), sv_0);
}

TEST(SvdpiSrcIncludeFile, TheFileDefinesTheTwoMacrosAndItsGuardOnly) {
  std::filesystem::path root(__FILE__);
  for (int level = 0; level < 4; ++level) root = root.parent_path();
  std::ifstream file(root / "src" / "simulator" / "svdpi_src.h");
  ASSERT_TRUE(file.is_open());
  std::vector<std::string> defined;
  std::string line;
  while (std::getline(file, line)) {
    std::istringstream words(line);
    std::string word;
    words >> word;
    EXPECT_NE(word, "typedef");
    EXPECT_NE(word, "extern");
    if (word != "#define") continue;
    words >> word;
    defined.push_back(word.substr(0, word.find('(')));
  }
  EXPECT_EQ(defined, (std::vector<std::string>{"INCLUDED_SVDPI_SRC",
                                               "SV_BIT_PACKED_ARRAY",
                                               "SV_LOGIC_PACKED_ARRAY"}));
}

}  // namespace
