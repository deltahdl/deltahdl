#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "fixture_preprocessor.h"

using namespace delta;

namespace {

TEST(CompilerDirectivePreprocessor, GraveAccentRequiredForDirective) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define MY_MAC 42\n"
      "int x = `MY_MAC;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("42"), std::string::npos);
}

TEST(CompilerDirectivePreprocessor, ApostropheIsNotGraveAccent) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define MY_MAC 42\n"
      "int x = 'MY_MAC;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  EXPECT_EQ(result.find("42"), std::string::npos);
  EXPECT_NE(result.find("'MY_MAC"), std::string::npos);
}

TEST(CompilerDirectivePreprocessor, EscapedBacktickInStringNotDirective) {
  PreprocFixture f;
  Preprocess("string s = \"value is \\`FOO\";\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(CompilerDirectivePreprocessor, DirectiveTakesEffectImmediately) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "`default_nettype none\n"
                           "`default_nettype wire\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultNetType(), NetType::kWire);
}

TEST(CompilerDirectivePreprocessor, DirectivePersistsAcrossModules) {
  auto r = ParseWithPreprocessor(
      "`define WIDTH 8\n"
      "module m1;\n"
      "  localparam W1 = `WIDTH;\n"
      "endmodule\n"
      "module m2;\n"
      "  localparam W2 = `WIDTH;\n"
      "endmodule\n"
      "module m3;\n"
      "  localparam W3 = `WIDTH;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 3u);
}

TEST(CompilerDirectivePreprocessor, MultipleDirectivesAllInEffect) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "`default_nettype none\n"
                           "`celldefine\n"
                           "`timescale 1ns / 1ps\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultNetType(), NetType::kNone);
  EXPECT_TRUE(pp.InCelldefine());
  EXPECT_TRUE(pp.HasTimescale());
}

TEST(CompilerDirectivePreprocessor, DirectivePersistsAcrossFiles) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});

  auto fid1 = f.mgr.AddFile("<file1>", "`default_nettype none\n");
  pp.Preprocess(fid1);
  EXPECT_EQ(pp.DefaultNetType(), NetType::kNone);

  auto fid2 = f.mgr.AddFile("<file2>", "module m; endmodule\n");
  pp.Preprocess(fid2);
  EXPECT_EQ(pp.DefaultNetType(), NetType::kNone);
}

TEST(CompilerDirectivePreprocessor, DirectiveDoesNotAffectOtherCU) {
  auto r1 = ParseWithPreprocessor(
      "`define FOO 1\n"
      "module m1;\n"
      "  localparam X = `FOO;\n"
      "endmodule\n");
  EXPECT_FALSE(r1.has_errors);

  auto r2 = ParseWithPreprocessor(
      "module m2;\n"
      "  localparam Y = `FOO;\n"
      "endmodule\n");

  EXPECT_TRUE(r2.has_errors);
}

}  // namespace
