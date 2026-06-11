#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_program.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// Exercises the syntax of the `encoding` protect pragma keyword (§34.5.9.1). The
// syntax block defines the keyword expression as a parenthesized subkeyword
// list: `encoding = ( enctype = <string> [ , line_length = <number> ]
// [ , bytes = <number> ] )`. Protect pragmas are processed at the preprocessor
// stage, where the generic `pragma` handler recognizes the keyword expression
// and consumes the directive line, including the entire parenthesized value.
struct ProtectEncodingSyntaxTest : ::testing::Test {
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

// The fully populated `encoding = ( enctype = <string> , line_length =
// <number> , bytes = <number> )` keyword expression is accepted and the
// directive line is stripped, including every subkeyword and value.
TEST_F(ProtectEncodingSyntaxTest, PragmaProtectEncodingConsumed) {
  auto result = Preprocess(
      "`pragma protect encoding = ( enctype = \"base64\" , line_length = 64 , "
      "bytes = 128 )\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("encoding"), std::string::npos);
  EXPECT_EQ(result.find("base64"), std::string::npos);
}

// Only the encoding directive line is removed; neighboring source text survives,
// confirming it is the encoding keyword expression line that the pragma path
// consumes.
TEST_F(ProtectEncodingSyntaxTest, EncodingDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess(
      "module m;\n"
      "`pragma protect encoding = ( enctype = \"uuencode\" )\n"
      "endmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("uuencode"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

// The optional `line_length` and `bytes` subkeywords may be omitted: the minimal
// form carrying only the required `enctype` subkeyword is still recognized and
// the directive line is stripped in full.
TEST_F(ProtectEncodingSyntaxTest, EncodingMinimalEnctypeOnlyFormConsumed) {
  auto result = Preprocess("`pragma protect encoding = ( enctype = \"raw\" )\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("enctype"), std::string::npos);
}

// The two optional subkeywords are independent in the grammar
// (`[ , line_length ] [ , bytes ]`): a form that omits `line_length` but
// supplies `bytes` is a valid keyword expression and is consumed in full, just
// like the forms that include both or neither optional.
TEST_F(ProtectEncodingSyntaxTest, EncodingBytesWithoutLineLengthConsumed) {
  auto result =
      Preprocess("`pragma protect encoding = ( enctype = \"base64\" , bytes = "
                 "256 )\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("bytes"), std::string::npos);
}

}  // namespace
