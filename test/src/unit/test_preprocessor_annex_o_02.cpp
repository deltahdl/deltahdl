#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "preprocessor/protect_flow.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// The key the author encrypts under. §O.2 is about what the block protects,
// so one key serves every text here.
constexpr std::string_view kExchangeKey = "acme-exchange-key";

bool Holds(std::string_view text, std::string_view needle) {
  return text.find(needle) != std::string_view::npos;
}

// The one encrypted block a transformed text records, as §34.5.15 has it
// written: on the line beneath the data_block keyword standing alone.
std::string TheRecordedBlock(std::string_view transformed) {
  constexpr std::string_view kOpening = "`pragma protect data_block\n";
  size_t pos = transformed.find(kOpening);
  if (pos == std::string_view::npos) return "";
  size_t start = pos + kOpening.size();
  size_t close = transformed.find('\n', start);
  if (close == std::string_view::npos) close = transformed.size();
  return std::string(transformed.substr(start, close - start));
}

// §O.2: the data to be protected from inappropriate access or unauthorized
// modification is placed within a protect begin-end block, the block the
// protect pragma's begin and end delimit.
TEST(EncryptionFlowOverview, TheDataIsPlacedWithinAProtectBeginEndBlock) {
  EXPECT_EQ(KeywordOpeningTheProtectedBlock(), "begin");
  EXPECT_EQ(KeywordClosingTheProtectedBlock(), "end");
  auto threats = ThreatsTheBlockProtectsFrom();
  ASSERT_EQ(threats.size(), 2u);
  EXPECT_EQ(threats[0], ProtectionThreat::kInappropriateAccess);
  EXPECT_EQ(threats[1], ProtectionThreat::kUnauthorizedModification);
  EXPECT_TRUE(InformationInTheBlockIsProtectedOnceEncrypted());
}

// §O.2 against the encrypting flow: the data placed within the block is what
// the encryption protects. After the flow the text within the block is gone
// from the output, an encrypted block standing where it was, while the text
// placed outside the block -- which the author did not ask to protect -- is
// carried across as it was written.
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

// §O.2: information in the begin-end block, once encrypted, is also
// protected. A pragma expression the author writes inside the block -- here a
// licence -- and a note written beside the design are encrypted with the
// block rather than left in the clear, so the output carries neither, and
// both come back only under the key. The three expressions §34.5.5, §34.5.6
// and §34.5.30 have an envelope publish in the clear -- the author's name,
// what more the author offers and the documentation nothing interprets -- are
// the standard's own exception and are lifted out of the block by those
// subclauses, so none of them is written here.
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
