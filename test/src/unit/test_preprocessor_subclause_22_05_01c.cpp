#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/diagnostic.h"
#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

bool ErrorAtUnder(const PreprocFixture& f, uint32_t line,
                  const std::string& subclause) {
  for (const auto& d : f.diag.Diagnostics()) {
    if (d.severity == DiagSeverity::kError && d.loc.line == line &&
        d.subclause == subclause) {
      return true;
    }
  }
  return false;
}

TEST(MacroNameRestriction, EveryDirectiveNameIsRefusedAsAMacroName) {
  for (const char* name :
       {"__LINE__", "begin_keywords", "celldefine", "default_nettype", "else",
        "elsif", "end_keywords", "endcelldefine", "endif", "ifndef", "line",
        "nounconnected_drive", "pragma", "resetall", "timescale",
        "unconnected_drive", "undef", "undefineall"}) {
    PreprocFixture f;
    Preprocess(std::string("`define ") + name + " 1\n", f);
    std::string msg = "redefining compiler directive '";
    msg += name;
    msg += '\'';
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), msg, 1, "22.5.1")) << name;
  }
}

TEST(MacroNameRestriction, ANameThatIsNoDirectiveIsAccepted) {
  PreprocFixture f;
  auto out = Preprocess("`define line_count 1\nint v = `line_count;\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("int v = 1;"), std::string::npos) << out;
}

struct PlacedDefine {
  const char* where;
  const char* opener;
  const char* closer;
};

TEST(DefineInsideDesignElements, DefinedThenUsedInsideEachElement) {
  for (const auto& p : {
           PlacedDefine{"package", "package p;\n", "endpackage\n"},
           PlacedDefine{"interface", "interface i;\n", "endinterface\n"},
           PlacedDefine{"program", "program g;\n", "endprogram\n"},
           PlacedDefine{"checker", "checker c;\n", "endchecker\n"},
           PlacedDefine{"class", "class k;\n", "endclass\n"},
           PlacedDefine{"generate block", "module m;\nif (1) begin : b\n",
                        "end\nendmodule\n"},
           PlacedDefine{"function", "module m;\nfunction int f();\n",
                        "endfunction\nendmodule\n"},
           PlacedDefine{"task", "module m;\ntask t();\n",
                        "endtask\nendmodule\n"},
       }) {
    PreprocFixture f;
    std::string src = p.opener;
    src += "`define PLACED 31\nint v = `PLACED;\n";
    src += p.closer;
    auto out = Preprocess(src, f);
    EXPECT_FALSE(f.diag.HasErrors()) << p.where;
    EXPECT_NE(out.find("int v = 31;"), std::string::npos) << p.where << out;
  }
}

TEST(MacroFormalNames, DISABLED_AnEscapedFormalNameIsRefused) {
  PreprocFixture f;
  Preprocess("`define M(\\x ) 1\n", f);
  EXPECT_TRUE(ErrorAtUnder(f, 1, "22.5.1"));
}

TEST(MacroFormalNames, DISABLED_AFormalThatIsNoIdentifierIsRefused) {
  PreprocFixture f;
  Preprocess("`define M(1) x\n", f);
  EXPECT_TRUE(ErrorAtUnder(f, 1, "22.5.1"));
}

TEST(MacroFormalNames, ASimpleFormalNameIsAccepted) {
  PreprocFixture f;
  auto out = Preprocess("`define M(x) x\nint v = `M(4);\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("int v = 4;"), std::string::npos) << out;
}

TEST(MacroFormalNames, DISABLED_AnEmptyFormalListIsRefused) {
  PreprocFixture f;
  Preprocess("`define M() 5\n", f);
  EXPECT_TRUE(ErrorAtUnder(f, 1, "22.5.1"));
}

TEST(MacroFormalNames, AOneFormalListIsAccepted) {
  PreprocFixture f;
  Preprocess("`define M(a) 5\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(MacroFormalList, AnEscapedNameThenSpacesDefinesAnObjectLikeMacro) {
  PreprocFixture f;
  auto out = Preprocess("`define \\M@  (a) a\nx = `\\M@ ;\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("x = (a) a"), std::string::npos) << out;
}

TEST(MacroFormalList, AnExplicitlyEmptyLastDefaultExpandsToNothing) {
  PreprocFixture f;
  auto out =
      Preprocess("`define M(a, b=) [a|b]\nx = `M(7, );\ny = `M(8);\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("x = [7|];"), std::string::npos) << out;
  EXPECT_NE(out.find("y = [8|];"), std::string::npos) << out;
}

}  // namespace
