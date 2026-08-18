#include <gtest/gtest.h>

#include <string>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "fixture_program.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// Exercises the syntax of the `data_block` protect pragma keyword
// (§34.5.15.1). The syntax block defines the keyword as the bare word
// `data_block` with no arguments. Protect pragmas are processed at the
// preprocessor stage, where the generic `pragma` handler recognizes the
// keyword and consumes the directive line.
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

// The bare `data_block` keyword is accepted and the directive line is
// stripped.
TEST_F(ProtectDataBlockSyntaxTest, PragmaProtectDataBlockConsumed) {
  auto result = Preprocess("`pragma protect data_block\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
}

// Only the data_block directive line is removed; neighboring source text
// survives, confirming it is the data_block keyword line that the pragma
// path consumes.
TEST_F(ProtectDataBlockSyntaxTest,
       DataBlockDirectiveStrippedSurroundingTextKept) {
  auto result =
      Preprocess("module m;\n`pragma protect data_block\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

// The cases above observe the directive line going away. What §34.5.15.1
// defines is the spelling -- the keyword standing alone, with §34.5.15.2
// putting the block on the lines beneath it -- and this implementation writes
// the block as the keyword's own value instead, reading it back the same way.
// An envelope in the spelling the standard defines therefore carries a block
// this tool cannot reach, and the cases below hold it to saying so rather than
// passing such an envelope over with the design inside it never appearing.

// A decryption envelope as another tool wrote it, holding `described`.
std::string ForeignEnvelope(const std::string& described) {
  std::string text = "`pragma protect begin_protected\n";
  text.append(described);
  text.append("`pragma protect end_protected\n");
  return text;
}

// §34.5.15.1: the keyword standing alone inside a protected envelope is the
// spelling the standard defines, and it is one this implementation does not
// read. It is reported where it stands.
TEST(ProtectDataBlockSyntax, TheKeywordAloneIsReportedAsASpellingWeDoNotRead) {
  std::string src = ForeignEnvelope(
      "`pragma protect data_block\n"
      "SGVsbG8sIHNlYWxlZCB3b3JsZA==\n");
  PreprocFixture f;
  Preprocess(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "not a spelling this implementation reads",
                            LineHolding(src, "data_block"), "34.5.15.1"));
}

// The same keyword outside every envelope. §34.5.15.2 makes a block outside a
// previously generated envelope an error of its own, reported elsewhere, and
// what this case fixes is that the spelling report belongs to a block standing
// where a block belongs rather than to the word wherever it appears.
TEST(ProtectDataBlockSyntax, TheKeywordAloneOutsideAnEnvelopeIsNotThisReport) {
  PreprocFixture f;
  Preprocess("`pragma protect data_block\n", f);
  for (const auto& d : f.diag.Diagnostics()) {
    EXPECT_EQ(d.message.find("not a spelling this implementation reads"),
              std::string::npos)
        << d.message;
  }
}

}  // namespace
