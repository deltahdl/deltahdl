#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "preprocessor/protect_flow.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

constexpr std::string_view kExchangeKey = "acme-exchange-key";

bool Holds(std::string_view text, std::string_view needle) {
  return text.find(needle) != std::string_view::npos;
}

std::string TheRecordedBlock(std::string_view transformed) {
  constexpr std::string_view kOpening = "`pragma protect data_block\n";
  size_t pos = transformed.find(kOpening);
  if (pos == std::string_view::npos) return "";
  size_t start = pos + kOpening.size();
  size_t close = transformed.find('\n', start);
  if (close == std::string_view::npos) close = transformed.size();
  return std::string(transformed.substr(start, close - start));
}

TEST(EncryptionFlowOverview, TheDataIsPlacedWithinAProtectBeginEndBlock) {
  EXPECT_EQ(KeywordOpeningTheProtectedBlock(), "begin");
  EXPECT_EQ(KeywordClosingTheProtectedBlock(), "end");
  auto threats = ThreatsTheBlockProtectsFrom();
  ASSERT_EQ(threats.size(), 2u);
  EXPECT_EQ(threats[0], ProtectionThreat::kInappropriateAccess);
  EXPECT_EQ(threats[1], ProtectionThreat::kUnauthorizedModification);
  EXPECT_TRUE(InformationInTheBlockIsProtectedOnceEncrypted());
}

TEST(EncryptionFlowOverview, WhatIsPlacedWithinTheBlockIsWhatIsProtected) {
  std::string written = EncryptEnvelopes(
      "module m;\n"
      "`pragma protect begin\n"
      "  localparam SECRET = 42;\n"
      "`pragma protect end\n"
      "endmodule\n",
      kExchangeKey);
  EXPECT_TRUE(Holds(written, "module m;\n"));
  EXPECT_TRUE(Holds(written, "endmodule\n"));
  EXPECT_FALSE(Holds(written, "localparam SECRET"));
  std::string cleartext;
  ASSERT_TRUE(DecryptProtectedRegion(TheRecordedBlock(written), kExchangeKey,
                                     &cleartext));
  EXPECT_EQ(cleartext, "  localparam SECRET = 42;\n");
}

TEST(EncryptionFlowOverview, InformationInTheBlockIsProtectedOnceEncrypted) {
  std::string written = EncryptEnvelopes(
      "`pragma protect begin\n"
      "`pragma protect runtime_license=(library=\"lic.so\", "
      "entry=\"acquire\", feature=\"simulate\")\n"
      "  // proprietary: the phase detector's gain schedule\n"
      "  initial result = 42;\n"
      "`pragma protect end\n",
      kExchangeKey);
  EXPECT_FALSE(Holds(written, "lic.so"));
  EXPECT_FALSE(Holds(written, "gain schedule"));
  std::string cleartext;
  ASSERT_TRUE(DecryptProtectedRegion(TheRecordedBlock(written), kExchangeKey,
                                     &cleartext));
  EXPECT_TRUE(Holds(cleartext, "library=\"lic.so\""));
  EXPECT_TRUE(Holds(cleartext, "gain schedule"));
  EXPECT_FALSE(DecryptProtectedRegion(TheRecordedBlock(written),
                                      "not-the-authors-key", &cleartext));
}

}  // namespace
