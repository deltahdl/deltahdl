#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <utility>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

struct ProtectDataBlockSyntaxTest : ::testing::Test {
 protected:
  std::string Preprocess(const std::string& src) {
    auto fid = mgr_.AddFile("<test>", src);
    Preprocessor pp(mgr_, diag_, config_);
    return pp.Preprocess(fid);
  }

  SourceManager mgr_;
  DiagEngine diag_{mgr_};
  PreprocConfig config_;
};

namespace {

TEST_F(ProtectDataBlockSyntaxTest, PragmaProtectDataBlockConsumed) {
  auto result = Preprocess("`pragma protect data_block\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
}

TEST_F(ProtectDataBlockSyntaxTest,
       DataBlockDirectiveStrippedSurroundingTextKept) {
  auto result =
      Preprocess("module m;\n`pragma protect data_block\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

constexpr std::string_view kOpenedDesign =
    "module recovered_design_m; endmodule\n";
constexpr std::string_view kSyntaxRegionKey = "one-key-for-the-syntax-case";

constexpr std::string_view kUnopenableBlock = "AAAA";

std::string ForeignEnvelope(const std::string& described) {
  std::string text = "`pragma protect begin_protected\n";
  text.append(described);
  text.append("`pragma protect end_protected\n");
  return text;
}

TEST(ProtectDataBlockSyntax, TheKeywordAloneTakesTheLineBeneathItAsTheBlock) {
  PreprocFixture f;
  std::string described = "`pragma protect data_block\n";
  described.append(kUnopenableBlock).append("\n");
  std::string read = Preprocess(ForeignEnvelope(described), f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied", 3,
      "34.3.2"));
  EXPECT_EQ(read.find(kUnopenableBlock), std::string::npos) << read;
  EXPECT_EQ(read.find("data_block"), std::string::npos) << read;
}

TEST(ProtectDataBlockSyntax, TheKeywordCarryingAValueSpeaksForNoLine) {
  PreprocFixture f;
  std::string described = "`pragma protect data_block=\"a-value-of-its-own\"\n";
  described.append(kUnopenableBlock).append("\n");
  std::string read = Preprocess(ForeignEnvelope(described), f);
  EXPECT_NE(read.find(kUnopenableBlock), std::string::npos) << read;
}

TEST(ProtectDataBlockSyntax, TheKeywordAloneEndsAtTheComma) {
  PreprocFixture f;
  std::string described =
      "`pragma protect data_block, data_method=\"aes128-cbc\"\n";
  described.append(kUnopenableBlock).append("\n");
  Preprocess(ForeignEnvelope(described), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "data block states an encryption algorithm this "
                            "implementation does not provide: aes128-cbc",
                            3, "34.5.11.2"));
}

TEST(ProtectDataBlockSyntax, TheBlockBeneathTheKeywordAloneIsRecovered) {
  std::string envelope = "`pragma protect begin_protected\n";
  envelope.append("`pragma protect data_block\n");
  envelope.append(EncryptProtectedRegion(kOpenedDesign, kSyntaxRegionKey));
  envelope.append("\n`pragma protect end_protected\n");

  PreprocFixture f;
  PreprocConfig config;
  config.protect_key = std::string(kSyntaxRegionKey);
  std::string read = Preprocess(envelope, f, config);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(read.find(kOpenedDesign), std::string::npos) << read;
  EXPECT_EQ(read.find("data_block"), std::string::npos) << read;
}

constexpr std::string_view kOriginRegionKey = "one-key-for-the-origin-cases";

std::string FirstErrorLocationOf(const std::string& src, PreprocFixture& f,
                                 Arena& arena) {
  auto fid = f.mgr.AddFile("design.sv", src);
  PreprocConfig config;
  config.protect_key = std::string(kOriginRegionKey);
  Preprocessor pp(f.mgr, f.diag, std::move(config));
  std::string out = pp.Preprocess(fid);
  auto out_fid =
      f.mgr.AddPreprocessedFile("<preprocessed>", out, pp.LineOrigins());
  Lexer lexer(f.mgr.FileContent(out_fid), out_fid, f.diag,
              TextOrigin::kPreprocessorOutput);
  Parser parser(lexer, arena, f.diag);
  parser.Parse();
  for (const auto& d : f.diag.Diagnostics()) {
    if (d.severity == DiagSeverity::kError) return f.mgr.FormatLoc(d.loc);
  }
  return "<no error was reported>";
}

std::string SourceWithEnvelope(std::string_view region) {
  std::string src = "// one\n// two\n";
  src.append("`pragma protect begin_protected\n");
  src.append("`pragma protect data_block\n");
  src.append(EncryptProtectedRegion(region, kOriginRegionKey));
  src.append("\n`pragma protect end_protected\n");
  return src;
}

TEST(ProtectDataBlockOrigin, ARecoveredLineNamesItsEnvelopeAndItsOwnLine) {
  PreprocFixture f;
  Arena arena;
  std::string where = FirstErrorLocationOf(
      SourceWithEnvelope("module m;\nendmodule\n%\n"), f, arena);
  EXPECT_NE(where.find("<protected envelope at design.sv:"), std::string::npos)
      << where;
  EXPECT_NE(where.find(">:3:"), std::string::npos) << where;
}

TEST(ProtectDataBlockOrigin, ARecoveredLineMovesWithItsPositionInTheBlock) {
  PreprocFixture f;
  Arena arena;
  std::string where = FirstErrorLocationOf(
      SourceWithEnvelope("module m;\nendmodule\n\n%\n"), f, arena);
  EXPECT_NE(where.find(">:4:"), std::string::npos) << where;
}

TEST(ProtectDataBlockOrigin, ALineOutsideAnEnvelopeNamesItsOwnFile) {
  PreprocFixture f;
  Arena arena;
  std::string where =
      FirstErrorLocationOf("module m;\nendmodule\n%\n", f, arena);
  EXPECT_NE(where.find("design.sv:3:"), std::string::npos) << where;
  EXPECT_EQ(where.find("protected envelope"), std::string::npos) << where;
}

TEST(ProtectDataBlockOrigin, AnEnvelopeInsideAnEnvelopeNamesTheInnerBlock) {
  PreprocFixture f;
  Arena arena;
  std::string inner = SourceWithEnvelope("module m;\nendmodule\n%\n");
  std::string where = FirstErrorLocationOf(SourceWithEnvelope(inner), f, arena);
  EXPECT_NE(where.find("<protected envelope at <protected envelope at "
                       "design.sv:"),
            std::string::npos)
      << where;
  EXPECT_NE(where.find(">:3:"), std::string::npos) << where;
}

}  // namespace
