#include <gtest/gtest.h>

#include <string>

#include "common/types.h"
#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"

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

TEST(Preprocessor, DefaultNettype_IllegalInsideDesignElement) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("module foo;\n`default_nettype none\nendmodule\n", f, pp);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`default_nettype illegal inside a design element",
                            2, "22.8"));
}

TEST(Preprocessor, DefaultNettype_InvalidType) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_nettype bogus\n", f, pp);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "invalid net type 'bogus'", 1,
                            "22.8"));
}

TEST(Preprocessor, DefaultNettype_LatestDirectiveWins) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_nettype none\n`default_nettype tri\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultNetType(), NetType::kTri);
}

TEST(Preprocessor, DefaultNettype_DefaultIsWire) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("// no directives\n", f, pp);
  EXPECT_EQ(pp.DefaultNetType(), NetType::kWire);
}

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

TEST(Preprocessor, DefaultNettype_MissingArgument) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_nettype\n", f, pp);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "invalid net type ''", 1, "22.8"));
}

TEST(Preprocessor, DefaultNettype_ResetallRestoresWire) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`default_nettype none\n"
      "`resetall\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultNetType(), NetType::kWire);
}

TEST(Preprocessor, DefaultNettype_Supply0Invalid) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_nettype supply0\n", f, pp);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "invalid net type 'supply0'",
                            1, "22.8"));
}

TEST(Preprocessor, DefaultNettype_Supply1Invalid) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_nettype supply1\n", f, pp);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "invalid net type 'supply1'",
                            1, "22.8"));
}

TEST(Preprocessor, DefaultNettype_RecordedAtEachHeader) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`default_nettype tri1\n"
      "module a;\nendmodule\n"
      "`default_nettype tri0\n"
      "interface b;\nendinterface\n"
      "`default_nettype wire\n"
      "program c;\nendprogram\n"
      "`default_nettype none\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  const auto& list = pp.ModuleDirectivesList();
  ASSERT_EQ(list.size(), 3u);
  EXPECT_EQ(list[0].default_nettype, NetType::kTri1);
  EXPECT_EQ(list[1].default_nettype, NetType::kTri0);
  EXPECT_EQ(list[2].default_nettype, NetType::kWire);
  EXPECT_EQ(pp.DefaultNetType(), NetType::kNone);
}

TEST(Preprocessor, DefaultNettype_InterconnectIsRejected) {
  PreprocFixture f;
  Preprocess("`default_nettype interconnect\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "invalid net type 'interconnect'", 1, "22.8"));
}

TEST(Preprocessor, DefaultNettype_AUserDefinedNettypeIsRejected) {
  PreprocFixture f;
  Preprocess("nettype logic mynet;\n`default_nettype mynet\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "invalid net type 'mynet'", 2,
                            "22.8"));
}

struct PlacedNettype {
  const char* src;
  int line;
};

TEST(Preprocessor, DefaultNettype_RejectedInsideEveryDesignElement) {
  for (const auto& c : {
           PlacedNettype{"interface i;\n`default_nettype wire\nendinterface\n",
                         2},
           PlacedNettype{"program p;\n`default_nettype wire\nendprogram\n", 2},
           PlacedNettype{"package k;\n`default_nettype wire\nendpackage\n", 2},
           PlacedNettype{"checker c;\n`default_nettype wire\nendchecker\n", 2},
           PlacedNettype{"primitive u(output o, input a);\n"
                         "`default_nettype wire\n"
                         "table 0:0; 1:1; endtable\nendprimitive\n",
                         2},
           PlacedNettype{"config cf;\n`default_nettype wire\ndesign t;\n"
                         "endconfig\n",
                         2},
           PlacedNettype{"module outer;\nmodule inner;\nendmodule\n"
                         "`default_nettype wire\nendmodule\n",
                         4},
           PlacedNettype{"`define DN `default_nettype wire\nmodule m;\n`DN\n"
                         "endmodule\n",
                         3},
       }) {
    PreprocFixture f;
    Preprocess(c.src, f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "`default_nettype illegal inside a design "
                              "element",
                              c.line, "22.8"))
        << c.src;
  }
}

TEST(Preprocessor, DefaultNettype_AcceptedInsideAClassAtCompilationUnitScope) {
  PreprocFixture f;
  Preprocess("class k;\n`default_nettype wire\nendclass\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}
