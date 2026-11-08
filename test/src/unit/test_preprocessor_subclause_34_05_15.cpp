#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_protect_read.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"

using namespace delta;

namespace {

constexpr std::string_view kFirstBlockCharacters = "NOTABLOCKOFANYENVELOPE";
constexpr std::string_view kSecondBlockCharacters = "NORISTHISABLOCKOFANY";

std::string BlockWriting(std::string_view characters) {
  std::string text = "`pragma protect data_block\n";
  text.append(characters).append("\n");
  return text;
}

constexpr std::string_view kEncodingSealedDesign = "  initial result = 42;\n";

std::string SealedModel(std::string_view inside) {
  std::string text = "`pragma protect begin_protected\n";
  text.append(inside);
  text.append("`pragma protect end_protected\n");
  return text;
}

std::string Region(std::string_view inside) {
  std::string text = "`pragma protect begin\n";
  text.append(inside).append(kEncodingSealedDesign);
  text.append("`pragma protect end\n");
  return text;
}

TEST(ProtectDataBlockEncryptionInput, ABlockContainedByNothingIsReported) {
  std::string src = "module m;\n";
  src.append(BlockWriting(kFirstBlockCharacters));
  src.append("endmodule\n");
  EncryptionRun run(src);
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            "data_block is written where no previously", 2,
                            "34.5.15"));
}

TEST(ProtectDataBlockEncryptionInput, TheReportedTextIsHandedBackUnchanged) {
  std::string src = "module m;\n";
  src.append(BlockWriting(kFirstBlockCharacters));
  src.append("endmodule\n");
  EncryptionRun run(src);
  EXPECT_EQ(run.text, src);
  EXPECT_TRUE(
      ReportedError(run.diag.Diagnostics(),
                    "protect pragma data_block is written where no previously "
                    "generated begin_protected-end_protected block contains it",
                    2, "34.5.15"));
}

TEST(ProtectDataBlockEncryptionInput, EachBlockContainedByNothingIsReported) {
  std::string src(BlockWriting(kFirstBlockCharacters));
  src.append(BlockWriting(kSecondBlockCharacters));
  EncryptionRun run(src);
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            "data_block is written where no previously", 1,
                            "34.5.15"));
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            "data_block is written where no previously", 3,
                            "34.5.15"));
}

TEST(ProtectDataBlockEncryptionInput, ABlockInsideARegionToSealIsReportedToo) {
  std::string src = Region(BlockWriting(kFirstBlockCharacters));
  EncryptionRun run(src);
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            "data_block is written where no previously", 2,
                            "34.5.15"));
}

TEST(ProtectDataBlockEncryptionInput, ABlockASealedModelContainsIsIgnored) {
  EncryptionRun run(SealedModel(BlockWriting(kFirstBlockCharacters)));
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
}

TEST(ProtectDataBlockEncryptionInput, ASealedModelInsideARegionCarriesItsOwn) {
  EncryptionRun run(Region(SealedModel(BlockWriting(kFirstBlockCharacters))));
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
  EXPECT_FALSE(Holds(run.text, kFirstBlockCharacters));
}

TEST(ProtectDataBlockEncryptionInput, ABlockPastTheSealedModelIsReported) {
  std::string src(SealedModel(BlockWriting(kFirstBlockCharacters)));
  src.append(BlockWriting(kSecondBlockCharacters));
  EncryptionRun run(src);
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(), "data_block is written where no previously",
      LineHolding(src, kSecondBlockCharacters) - 1, "34.5.15"));
}

}  // namespace
