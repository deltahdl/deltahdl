#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_program.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// IEEE 1800-2023 §34.5.11 data_method.
//
// §34.5.11.1 Syntax declares the protect pragma expression
//   data_method = <string>
// and §34.5.11.2 describes its meaning. Every normative statement in the
// subclause is gated on an encryption- or decryption-providing tool:
//   - ENCRYPTION INPUT: the named method "shall be used to encrypt" the
//     following begin-end block (and the Table 34-3 identifier registry that
//     constrains the legal string values) applies only to a tool that performs
//     encryption.
//   - ENCRYPTION OUTPUT: "shall be unchanged in the output file ..." applies
//     only to such a tool.
//   - DECRYPTION INPUT: the method "should" be used to decrypt the data_block,
//     gated on a tool that performs decryption.
// This implementation provides neither an encryption nor a decryption engine,
// so all of those statements are vacuously satisfied. The one observable
// behaviour is that the data_method protect pragma expression, a string-valued
// pragma like every other protect keyword, is consumed by the generic `pragma`
// directive handler so it never leaks into the token stream handed downstream.

struct ProtectedTest : ::testing::Test {
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

// §34.5.11.1 Syntax: the data_method pragma expression is recognised and
// consumed by the preprocessor without error, regardless of which Table 34-3
// identifier string it names.
TEST_F(ProtectedTest, PragmaProtectDataMethodConsumed) {
  auto result = Preprocess("`pragma protect data_method=\"des-cbc\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
}

// The string value is treated uniformly as <string>: an optional Table 34-3
// identifier is consumed exactly like the required one, and the directive is
// stripped while surrounding cleartext is preserved.
TEST_F(ProtectedTest, DataMethodConsumedKeepsSurroundingText) {
  auto result = Preprocess(
      "before_text\n"
      "`pragma protect data_method=\"aes256-cbc\"\n"
      "after_text\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("before_text"), std::string::npos);
  EXPECT_NE(result.find("after_text"), std::string::npos);
}

}
