// Tests for §34 Protected envelopes — preprocessor pragma protect handling

#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

namespace {

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

// =============================================================================
// §34.4 Pragma protect directive recognition
// =============================================================================

TEST_F(ProtectedTest, PragmaProtectConsumed) {
  auto result = Preprocess("`pragma protect begin\n");
  EXPECT_FALSE(diag_.HasErrors());
  // Pragma line should be consumed (not appear in output).
  EXPECT_EQ(result.find("pragma"), std::string::npos);
}

TEST_F(ProtectedTest, PragmaProtectEndConsumed) {
  auto result = Preprocess("`pragma protect end\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
}

// =============================================================================
// §34.5.1/2 Protected envelope begin/end parsing
// =============================================================================

TEST_F(ProtectedTest, BeginEndEnvelope) {
  auto result = Preprocess(
      "module m;\n"
      "`pragma protect begin\n"
      "  logic secret_wire;\n"
      "`pragma protect end\n"
      "endmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  // Non-pragma lines should pass through.
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("logic secret_wire;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
  // Pragma lines consumed.
  EXPECT_EQ(result.find("pragma"), std::string::npos);
}

// =============================================================================
// §34.5.3/4 Protected region with encoding (begin_protected/end_protected)
// =============================================================================

TEST_F(ProtectedTest, ProtectedRegionWithEncoding) {
  auto result = Preprocess(
      "`pragma protect encoding=(enctype=\"raw\")\n"
      "`pragma protect data_method=\"x-caesar\"\n"
      "`pragma protect begin_protected\n"
      "`pragma protect data_block\n"
      "encrypted_data_here\n"
      "`pragma protect end_protected\n");
  EXPECT_FALSE(diag_.HasErrors());
  // All pragma lines consumed.
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  // Non-pragma content passes through (encrypted data).
  EXPECT_NE(result.find("encrypted_data_here"), std::string::npos);
}

// =============================================================================
// §34.5 Key block recognition
// =============================================================================

TEST_F(ProtectedTest, KeyBlockPragma) {
  auto result = Preprocess(
      "`pragma protect key_keyowner=\"Acme\"\n"
      "`pragma protect key_method=\"rsa\"\n"
      "`pragma protect key_block\n"
      "base64encodedkeydata\n"
      "`pragma protect end_protected\n");
  EXPECT_FALSE(diag_.HasErrors());
  // Pragma lines consumed.
  EXPECT_EQ(result.find("key_keyowner"), std::string::npos);
  EXPECT_EQ(result.find("key_method"), std::string::npos);
}

// =============================================================================
// §34.5 Viewport support
// =============================================================================

TEST_F(ProtectedTest, ViewportPragma) {
  auto result = Preprocess(
      "`pragma protect viewport=all\n"
      "module m;\n"
      "endmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("viewport"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
}

// =============================================================================
// §34.5 Reset directive
// =============================================================================

TEST_F(ProtectedTest, ResetDirective) {
  auto result = Preprocess(
      "`pragma protect begin\n"
      "  wire secret;\n"
      "`pragma protect end\n"
      "`pragma reset protect\n"
      "module m;\n"
      "endmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  // All pragma lines consumed. `pragma reset protect is also consumed.
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
}

// =============================================================================
// §34.5 License checking stub
// =============================================================================

TEST_F(ProtectedTest, RuntimeLicensePragma) {
  auto result = Preprocess(
      "`pragma protect runtime_license=(library=\"lic.so\","
      "feature=\"runSecret\",entry=\"chk\",match=42)\n"
      "module m;\n"
      "endmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("runtime_license"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
}

TEST_F(ProtectedTest, DecryptLicensePragma) {
  auto result = Preprocess(
      "`pragma protect decrypt_license=(library=\"lic.so\","
      "feature=\"decryptIP\")\n"
      "module m;\n"
      "endmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("decrypt_license"), std::string::npos);
}

}  // namespace
