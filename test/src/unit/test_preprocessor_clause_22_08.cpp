#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_preprocessor.h"
#include "helpers_parser_verify.h"

using namespace delta;

static std::string PreprocessWithPP(const std::string& src, PreprocFixture& f,
                                    Preprocessor& pp) {
  auto fid = f.mgr.AddFile("<test>", src);
  return pp.Preprocess(fid);
}

TEST(Preprocessor, DefaultNettype_Wire) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_nettype wire\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultNetType(), NetType::kWire);
}

TEST(Preprocessor, DefaultNettype_None) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_nettype none\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());

  EXPECT_EQ(pp.DefaultNetType(), NetType::kNone);
}

TEST(Preprocessor, DefaultNettype_Tri) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_nettype tri\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultNetType(), NetType::kTri);
}

TEST(Preprocessor, DefaultNettypeTrireg) {
  PreprocFixture f;
  Preprocess("`default_nettype trireg\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}
TEST(ParserSection6, DefaultNettypeAffectsImplicit) {
  auto r = ParseWithPreprocessor(
      "`default_nettype none\n"
      "module m;\n"
      "  wire w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection22, DefaultNettypeModuleCount) {
  auto r = ParseWithPreprocessor(
      "`default_nettype wire\n"
      "module m1;\n"
      "endmodule\n"
      "`default_nettype none\n"
      "module m2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->name, "m1");
  EXPECT_EQ(r.cu->modules[1]->name, "m2");
}

TEST(ParserSection6, DefaultNettypeWire) {
  auto r = ParseWithPreprocessor(
      "`default_nettype wire\n"
      "module t;\n"
      "  assign out = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->default_nettype, NetType::kWire);
}
TEST(ParserSection6, DefaultNettypeNone) {
  auto r = ParseWithPreprocessor(
      "`default_nettype none\n"
      "module t;\n"
      "  wire explicit_w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
}

// --- §22.8: illegal inside a design element ---

TEST(Preprocessor, DefaultNettype_IllegalInsideDesignElement) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("module foo;\n`default_nettype none\nendmodule\n", f, pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

// --- §22.8: invalid net type name ---

TEST(Preprocessor, DefaultNettype_InvalidType) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_nettype bogus\n", f, pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

// --- §22.8: latest directive wins at preprocessor level ---

TEST(Preprocessor, DefaultNettype_LatestDirectiveWins) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_nettype none\n`default_nettype tri\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultNetType(), NetType::kTri);
}

// --- §22.8: default is wire when no directive ---

TEST(Preprocessor, DefaultNettype_DefaultIsWire) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("// no directives\n", f, pp);
  EXPECT_EQ(pp.DefaultNetType(), NetType::kWire);
}

// --- §22.8: all valid net types at preprocessor level ---

TEST(Preprocessor, DefaultNettype_Wand) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_nettype wand\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultNetType(), NetType::kWand);
}

TEST(Preprocessor, DefaultNettype_Wor) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_nettype wor\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultNetType(), NetType::kWor);
}

TEST(Preprocessor, DefaultNettype_Tri0) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_nettype tri0\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultNetType(), NetType::kTri0);
}

TEST(Preprocessor, DefaultNettype_Tri1) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_nettype tri1\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultNetType(), NetType::kTri1);
}

TEST(Preprocessor, DefaultNettype_Triand) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_nettype triand\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultNetType(), NetType::kTriand);
}

TEST(Preprocessor, DefaultNettype_Trior) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_nettype trior\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultNetType(), NetType::kTrior);
}

TEST(Preprocessor, DefaultNettype_Uwire) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_nettype uwire\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultNetType(), NetType::kUwire);
}

TEST(Preprocessor, DefaultNettype_Trireg) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_nettype trireg\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultNetType(), NetType::kTrireg);
}
