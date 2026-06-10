#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_program.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// IEEE 1800-2023 §34.5.12 data_keyname.
//
// §34.5.12.1 Syntax declares the protect pragma expression
//   data_keyname = <string>
// and §34.5.12.2 describes its meaning. Every normative statement in the
// subclause is gated on a tool that performs encryption or decryption of a
// protected envelope:
//   - ENCRYPTION INPUT: the name identifies a key (or key pair) for an
//     asymmetric algorithm that "should be used to decrypt the data_block",
//     and it "shall be an error" to name a key that is not known for the given
//     data_keyowner -- both apply only to an encrypting tool that owns a key
//     registry.
//   - ENCRYPTION OUTPUT: the encrypting tool "shall combine" the expression
//     with the named key and "shall" emit the data_keyname as cleartext (or,
//     under a digital envelope, encrypt it into the key_block) -- all gated on
//     a tool that produces an encryption output stream.
//   - DECRYPTION INPUT: the value is combined with the data_keyowner to select
//     the single key that "shall be used to decrypt the data_block", gated on a
//     tool that performs decryption.
// This implementation provides neither an encryption nor a decryption engine
// (no data_keyname, data_keyowner, or key_block handling exists in the source
// tree), so all of those statements are vacuously satisfied. The one observable
// behaviour is that the data_keyname protect pragma expression, a string-valued
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

// §34.5.12.1 Syntax: the data_keyname pragma expression is recognised and
// consumed by the preprocessor without error, whatever string names the key.
TEST_F(ProtectedTest, PragmaProtectDataKeynameConsumed) {
  auto result = Preprocess("`pragma protect data_keyname=\"acme_rsa_key\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
}

// The string value is treated uniformly as <string>: the directive is stripped
// while surrounding cleartext on neighbouring lines is preserved.
TEST_F(ProtectedTest, DataKeynameConsumedKeepsSurroundingText) {
  auto result = Preprocess(
      "before_text\n"
      "`pragma protect data_keyname=\"widgets_inc_key\"\n"
      "after_text\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("before_text"), std::string::npos);
  EXPECT_NE(result.find("after_text"), std::string::npos);
}

}
