#include <gtest/gtest.h>

#include <string>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "fixture_program.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"

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

// The cases above observe the directive line going away, which any directive
// the pragma handler consumes does. What §34.5.15.1 defines is the spelling:
// the keyword and nothing else, with §34.5.15.2 putting the block on the lines
// beneath it.
//
// This implementation writes the block as the keyword's own value and reads it
// back that way, so an envelope in the spelling the standard defines carries a
// block it cannot reach. That divergence is #3272, and it is not something a
// case here can assert away; what these cases do state is that the word itself
// is read as the keyword §34.4 tabulates, standing alone as its own subclause
// spells it, wherever a directive may put it.

// A decryption envelope as another tool wrote it, holding `described`.
std::string ForeignEnvelope(const std::string& described) {
  std::string text = "`pragma protect begin_protected\n";
  text.append(described);
  text.append("`pragma protect end_protected\n");
  return text;
}

// §34.5.15.1: the keyword standing alone is the spelling, and a directive
// carrying it is a protect pragma like any other -- it is consumed, and nothing
// of it is left in the text.
TEST(ProtectDataBlockSyntax, TheKeywordAloneIsConsumedInsideAnEnvelope) {
  PreprocFixture f;
  std::string read =
      Preprocess(ForeignEnvelope("`pragma protect data_block\n"), f);
  EXPECT_EQ(read.find("pragma"), std::string::npos) << read;
  EXPECT_EQ(read.find("data_block"), std::string::npos) << read;
}

// The keyword written as one expression of §22.11's comma-separated list, with
// a second expression after it. That expression takes effect, so the keyword
// standing alone ends at the comma rather than running on into it.
TEST(ProtectDataBlockSyntax, TheKeywordAloneEndsAtTheComma) {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp(mgr, diag, PreprocConfig{});
  pp.Preprocess(mgr.AddFile(
      "<test>", "`pragma protect data_block, data_method=\"des-cbc\"\n"));
  EXPECT_EQ(pp.ProtectKeywords().ValueOf("data_method").value, "des-cbc");
}

}  // namespace
