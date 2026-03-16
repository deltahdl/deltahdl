#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(DefaultNettypeElaboration, WireModuleElaboratesCorrectly) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`default_nettype wire\n"
      "module t;\n"
      "  parameter P = 7;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DefaultNettypeElaboration, NoneWithExplicitDeclsElaborates) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`default_nettype none\n"
      "module t;\n"
      "  wire w;\n"
      "  parameter P = 5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DefaultNettypeElaboration, LatestDirectiveWins) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`default_nettype none\n"
      "`default_nettype wire\n"
      "module t;\n"
      "  parameter P = 3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DefaultNettypeElaboration, ResetallRestoresWire) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`default_nettype none\n"
      "`resetall\n"
      "module t;\n"
      "  parameter P = 11;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
