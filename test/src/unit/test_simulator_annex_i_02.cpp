#include <gtest/gtest.h>

#include <array>
#include <cstdint>
#include <limits>
#include <string_view>
#include <type_traits>

#include "helpers_c_compiler.h"
#include "simulator/dpi_include_file.h"
#include "simulator/svdpi.h"

namespace {

TEST(SvdpiIncludeFileContract, IncludeFileIsProvided) {
  svScalar bit = sv_1;
  EXPECT_EQ(bit, 1);
}

TEST(SvdpiIncludeFileContract, AWidthTypeHoldsItsLargestValue) {
  uint8_t byte = 0xFFu;
  uint32_t word = 0xFFFFFFFFu;
  EXPECT_EQ(sizeof(byte), 1u);
  EXPECT_EQ(sizeof(word), 4u);
  EXPECT_EQ(byte, 0xFFu);
  EXPECT_EQ(word, 0xFFFFFFFFu);
}

TEST(SvdpiIncludeFileContract, AWidthTypeIsTheStandardLibrarysOwn) {
  EXPECT_TRUE((std::is_same<uint8_t, std::uint8_t>::value));
  EXPECT_TRUE((std::is_same<uint32_t, std::uint32_t>::value));
  EXPECT_FALSE(std::is_signed<uint8_t>::value);
  EXPECT_FALSE(std::is_signed<uint32_t>::value);
}

TEST(SvdpiIncludeFileContract, AWidthTypeWrapsAtItsWidth) {
  EXPECT_EQ(std::numeric_limits<uint8_t>::min(), 0u);
  EXPECT_EQ(std::numeric_limits<uint8_t>::max(), 255u);
  EXPECT_EQ(std::numeric_limits<uint32_t>::min(), 0u);
  EXPECT_EQ(std::numeric_limits<uint32_t>::max(), 4294967295u);

  uint8_t byte = std::numeric_limits<uint8_t>::max();
  uint32_t word = std::numeric_limits<uint32_t>::max();
  EXPECT_EQ(static_cast<uint8_t>(byte + 1u), 0u);
  EXPECT_EQ(static_cast<uint32_t>(word + 1u), 0u);
}

TEST(SvdpiIncludeFileContract, AScalarAndAChunkHaveTheSizesOfTheWidthTypes) {
  EXPECT_EQ(sizeof(svScalar), sizeof(uint8_t));
  EXPECT_EQ(sizeof(svBitVecVal), sizeof(uint32_t));
}

TEST(SvdpiIncludeFileContract, TheFileAloneDefinesTheWidthTypesInCxx) {
  CompilerResult run = CompileAsCxx(R"(#include "simulator/svdpi.h"
static_assert(sizeof(uint8_t) == 1 && sizeof(uint32_t) == 4, "width");
static_assert(static_cast<uint8_t>(-1) > 0, "unsigned");
static_assert(static_cast<uint32_t>(-1) > 0, "unsigned");
)");
  EXPECT_TRUE(run.succeeded) << run.output;
}

TEST(SvdpiIncludeFileContract, TheFileAloneDefinesTheWidthTypesInC) {
  CompilerResult run = CompileAsC(R"(#include "simulator/svdpi.h"
typedef char byte_width[sizeof(uint8_t) == 1 ? 1 : -1];
typedef char word_width[sizeof(uint32_t) == 4 ? 1 : -1];
typedef char byte_unsigned[(uint8_t)-1 > 0 ? 1 : -1];
typedef char word_unsigned[(uint32_t)-1 > 0 ? 1 : -1];
)");
  EXPECT_TRUE(run.succeeded) << run.output;
}

TEST(SvdpiIncludeFileContract, NoWidthTypeIsDefinedWithoutTheFile) {
  EXPECT_FALSE(CompileAsC("uint8_t byte;\n").succeeded);
  EXPECT_FALSE(CompileAsCxx("uint32_t word;\n").succeeded);
}

TEST(SvdpiIncludeFileContract, TheFileAloneServesAProgramWrittenInC) {
  CompilerResult run = CompileAsC(R"(#include "simulator/svdpi.h"
int serves(const svOpenArrayHandle array, svScope scope);
int serves(const svOpenArrayHandle array, svScope scope) {
  svBit bit = sv_1;
  svLogic logic = sv_x;
  svBitVecVal words[SV_PACKED_DATA_NELEMS(40)];
  svLogicVecVal chunk;
  words[0] = SV_GET_UNSIGNED_BITS(0xFFu, 4);
  words[1] = (svBitVecVal)SV_MASK(3);
  chunk.aval = words[0];
  chunk.bval = words[1];
  svPutBitselBit(words, 33, bit);
  svSetScope(scope);
  return svGetBitselLogic(&chunk, 0) + svSize(array, 1) + logic + sv_0 + sv_z;
}
)");
  EXPECT_TRUE(run.succeeded) << run.output;
}

TEST(SvdpiIncludeFileOverview, TheNormativeSectionIsMandatoryTheDeprecatedNot) {
  EXPECT_TRUE(delta::DpiSvdpiHIsProvidedByEverySimulator());
  EXPECT_TRUE(
      delta::DpiSvdpiSectionMustBeProvided(delta::DpiSvdpiSection::kNormative));
  EXPECT_FALSE(delta::DpiSvdpiSectionMustBeProvided(
      delta::DpiSvdpiSection::kDeprecated));
  EXPECT_TRUE(delta::DpiDeprecatedSectionIsDelimitedByComments());
}

TEST(SvdpiIncludeFileOverview, ThisFileOmitsTheDeprecatedSection) {
#ifdef INCLUDED_SVDPI_SV31A
  const bool kDeprecatedReached = true;
#else
  const bool kDeprecatedReached = false;
#endif
  EXPECT_FALSE(kDeprecatedReached);
}

TEST(SvdpiIncludeFileOverview, TheMethodDefiningTheWidthTypesIsNotPrescribed) {
  const std::array<std::string_view, 2> kTypes =
      delta::DpiWidthTypesImplementationsDefine();
  EXPECT_EQ(kTypes[0], "uint8_t");
  EXPECT_EQ(kTypes[1], "uint32_t");
  EXPECT_FALSE(delta::DpiWidthTypeDefinitionMethodIsPrescribed());
  EXPECT_EQ(sizeof(uint8_t), 1u);
  EXPECT_EQ(sizeof(uint32_t), 4u);
}

}  // namespace
