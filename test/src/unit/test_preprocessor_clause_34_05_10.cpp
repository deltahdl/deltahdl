#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_program.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// IEEE 1800-2023 §34.5.10 data_keyowner.
//
// §34.5.10.1 Syntax declares the protect pragma expression
//   data_keyowner = <string>
// and §34.5.10.2 describes its meaning. Every normative statement in the
// subclause is gated on a tool that performs encryption or decryption of a
// protected envelope:
//   - ENCRYPTION INPUT: the value names the legal entity or tool that provided
//     the keys, the encrypting tool "uses" it to select the encryption key, and
//     the data_keyname / data_decrypt_key / data_public_key values "shall be
//     unique" for the named owner -- all apply only to an encrypting tool that
//     owns a key registry.
//   - ENCRYPTION OUTPUT: the owner "shall be unchanged" in the output file
//     except when a digital signature encrypts it with the key_method into a
//     key_block -- gated on a tool that produces an encryption output stream.
//   - DECRYPTION INPUT: the owner is combined with the data_keyname or
//     data_public_key to select the secret/private key, gated on a tool that
//     performs decryption.
// This implementation provides neither an encryption nor a decryption engine
// (no data_keyowner, data_keyname, data_public_key, or key_block handling
// exists in the source tree), so all of those statements are vacuously
// satisfied. The one observable behaviour is that the data_keyowner protect
// pragma expression, a string-valued pragma like every other protect keyword,
// is consumed by the generic `pragma directive handler so it never leaks into
// the token stream handed downstream.

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

// §34.5.10.1 Syntax: the data_keyowner pragma expression is recognised and
// consumed by the preprocessor without error, whatever string names the owner.
TEST_F(ProtectedTest, PragmaProtectDataKeyownerConsumed) {
  auto result = Preprocess("`pragma protect data_keyowner=\"acme_corp\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
}

// The string value is treated uniformly as <string>: the directive is stripped
// while surrounding cleartext on neighbouring lines is preserved.
TEST_F(ProtectedTest, DataKeyownerConsumedKeepsSurroundingText) {
  auto result = Preprocess(
      "before_text\n"
      "`pragma protect data_keyowner=\"third_party_llc\"\n"
      "after_text\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("before_text"), std::string::npos);
  EXPECT_NE(result.find("after_text"), std::string::npos);
}

}
