#include <gtest/gtest.h>

#include <array>
#include <cstdint>
#include <limits>
#include <string_view>
#include <type_traits>

#include "simulator/dpi_include_file.h"
#include "simulator/svdpi.h"

namespace {

TEST(SvdpiIncludeFileContract, IncludeFileIsProvided) {
  svScalar bit = sv_1;
  EXPECT_EQ(bit, 1);
}

TEST(SvdpiIncludeFileContract, WidthTypesAreDefined) {
  uint8_t byte = 0xFFu;
  uint32_t word = 0xFFFFFFFFu;
  EXPECT_EQ(sizeof(byte), 1u);
  EXPECT_EQ(sizeof(word), 4u);
  EXPECT_EQ(byte, 0xFFu);
  EXPECT_EQ(word, 0xFFFFFFFFu);
}

TEST(SvdpiIncludeFileContract, WidthTypesAreUnsignedExactWidth) {
  EXPECT_TRUE((std::is_same<uint8_t, std::uint8_t>::value));
  EXPECT_TRUE((std::is_same<uint32_t, std::uint32_t>::value));
  EXPECT_FALSE(std::is_signed<uint8_t>::value);
  EXPECT_FALSE(std::is_signed<uint32_t>::value);
}

TEST(SvdpiIncludeFileContract, WidthTypesHaveExactValueRanges) {
  EXPECT_EQ(std::numeric_limits<uint8_t>::min(), 0u);
  EXPECT_EQ(std::numeric_limits<uint8_t>::max(), 255u);
  EXPECT_EQ(std::numeric_limits<uint32_t>::min(), 0u);
  EXPECT_EQ(std::numeric_limits<uint32_t>::max(), 4294967295u);

  uint8_t byte = std::numeric_limits<uint8_t>::max();
  uint32_t word = std::numeric_limits<uint32_t>::max();
  EXPECT_EQ(static_cast<uint8_t>(byte + 1u), 0u);
  EXPECT_EQ(static_cast<uint32_t>(word + 1u), 0u);
}

TEST(SvdpiIncludeFileContract, WidthTypesBackPublicDeclarations) {
  EXPECT_EQ(sizeof(svScalar), sizeof(uint8_t));
  EXPECT_EQ(sizeof(svBitVecVal), sizeof(uint32_t));
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

TEST(SvdpiIncludeFileOverview, TheWidthTypesAreDefinedByAnUnprescribedMethod) {
  const std::array<std::string_view, 2> kTypes =
      delta::DpiWidthTypesImplementationsDefine();
  EXPECT_EQ(kTypes[0], "uint8_t");
  EXPECT_EQ(kTypes[1], "uint32_t");
  EXPECT_FALSE(delta::DpiWidthTypeDefinitionMethodIsPrescribed());
  EXPECT_EQ(sizeof(uint8_t), 1u);
  EXPECT_EQ(sizeof(uint32_t), 4u);
}

}  // namespace
