#include <gtest/gtest.h>

#include <cstddef>
#include <string>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

size_t ErrorCount(const ElabFixture& f) {
  size_t n = 0;
  for (const auto& diag : f.diag.Diagnostics()) {
    if (diag.severity == DiagSeverity::kError) ++n;
  }
  return n;
}

std::string DynamicReport(const std::string& name) {
  return "references a member or element of the dynamic variable '" + name +
         "'";
}

std::string ForkReport(const std::string& block) {
  return "references an element of the fork-join block '" + block +
         "' of its enclosing scope";
}

std::string AutomaticReport(const std::string& name) {
  return "references the automatic variable '" + name +
         "' of its enclosing scope";
}

const char* const kEnclosing =
    "module m;\n"
    "  logic clk;\n"
    "  int q[$];\n"
    "  int fx[4];\n"
    "  initial fork : fa int v; join_any\n"
    "  initial fork : fn int w; join_none\n"
    "  task automatic t; int y; endtask\n"
    "  function automatic int f(); int y; return y; endfunction\n"
    "  function int g(); automatic int z; return z; endfunction\n"
    "  initial begin : b automatic int x = 1; int w; end\n";

std::string InModuleChecker(const std::string& body) {
  return std::string(kEnclosing) + "  checker c;\n" + body +
         "  endchecker\n  c u();\nendmodule\n";
}

void ExpectReportedAlone(const std::string& src, const std::string& report,
                         const std::string& at) {
  ElabFixture f;
  ElaborateSrc(src, f, "m");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), report, LineHolding(src, at), "17.2"))
      << src;
  EXPECT_EQ(ErrorCount(f), 1u) << src;
}

void ExpectAccepted(const std::string& src) {
  ElabFixture f;
  ElaborateSrc(src, f, "m");
  EXPECT_EQ(ErrorCount(f), 0u) << src;
}

TEST(CheckerEnclosingReference, TheEnclosingDeclarationsAreAccepted) {
  ExpectAccepted(
      InModuleChecker("    a1: assert property (@(posedge clk) 1);\n"));
}

TEST(CheckerEnclosingReference, DISABLED_AForkJoinAnyElementIsReportedAlone) {
  ExpectReportedAlone(
      InModuleChecker("    a1: assert property (@(posedge clk) fa.v == 1);\n"),
      ForkReport("fa"), "fa.v");
}

TEST(CheckerEnclosingReference, DISABLED_AForkJoinNoneElementIsReportedAlone) {
  ExpectReportedAlone(
      InModuleChecker("    a1: assert property (@(posedge clk) fn.w == 1);\n"),
      ForkReport("fn"), "fn.w");
}

TEST(CheckerEnclosingReference,
     DISABLED_AnAutomaticSubroutinesVariableIsReported) {
  ExpectReportedAlone(
      InModuleChecker("    a1: assert property (@(posedge clk) t.y == 1);\n"),
      AutomaticReport("y"), "t.y");
  ExpectReportedAlone(
      InModuleChecker("    a1: assert property (@(posedge clk) f.y == 1);\n"),
      AutomaticReport("y"), "f.y");
}

TEST(CheckerEnclosingReference, DISABLED_AnAutomaticVariableOfAStaticFunction) {
  ExpectReportedAlone(
      InModuleChecker("    a1: assert property (@(posedge clk) g.z == 1);\n"),
      AutomaticReport("z"), "g.z");
}

TEST(CheckerEnclosingReference, DISABLED_AnAutomaticVariableOfANamedBlock) {
  ExpectReportedAlone(
      InModuleChecker("    a1: assert property (@(posedge clk) b.x == 1);\n"),
      AutomaticReport("x"), "b.x");
}

TEST(CheckerEnclosingReference,
     DISABLED_AStaticVariableOfANamedBlockIsAccepted) {
  ExpectAccepted(
      InModuleChecker("    a1: assert property (@(posedge clk) b.w == 1);\n"));
}

TEST(CheckerEnclosingReference, AFixedSizeArrayElementIsAccepted) {
  ExpectAccepted(
      InModuleChecker("    bit v;\n"
                      "    always_comb v = fx[0];\n"
                      "    let l = fx[1];\n"
                      "    a1: assert #0 (fx[2] == 0);\n"
                      "    function int fn1(); return fx[3]; endfunction\n"));
}

void ExpectDynamicReportedAlone(const std::string& body) {
  ExpectReportedAlone(InModuleChecker(body), DynamicReport("q"), "q[0]");
}

TEST(CheckerEnclosingReference, DISABLED_ADynamicElementInEachProcedure) {
  for (const char* body :
       {"    bit v;\n    always_comb v = q[0];\n",
        "    bit v;\n    always_latch if (clk) v = q[0];\n",
        "    bit v;\n    always_ff @(posedge clk) v <= q[0];\n",
        "    initial a0: assert property (@(posedge clk) q[0] == 1);\n",
        "    final $display(\"%0d\", q[0]);\n",
        "    bit v;\n    assign v = q[0];\n"}) {
    ExpectDynamicReportedAlone(body);
  }
}

TEST(CheckerEnclosingReference, DISABLED_ADynamicElementInALet) {
  ExpectDynamicReportedAlone("    let l = q[0];\n");
}

TEST(CheckerEnclosingReference, ADynamicElementInANamedSequence) {
  ExpectDynamicReportedAlone(
      "    sequence s;\n      @(posedge clk) q[0] == 1;\n    endsequence\n"
      "    a3: assert property (s);\n");
}

TEST(CheckerEnclosingReference, DISABLED_ADynamicElementInANamedPropertyOnce) {
  ExpectDynamicReportedAlone(
      "    property p;\n      @(posedge clk) q[0] == 1;\n    endproperty\n"
      "    a3: assert property (p);\n");
}

TEST(CheckerEnclosingReference,
     DISABLED_ADynamicElementInEachDeferredAssertion) {
  for (const char* body : {"    a1: assert #0 (q[0] == 0);\n",
                           "    a1: assert final (q[0] == 0);\n",
                           "    m1: assume #0 (q[0] == 0);\n",
                           "    c1: cover #0 (q[0] == 0);\n"}) {
    ExpectDynamicReportedAlone(body);
  }
}

TEST(CheckerEnclosingReference, DISABLED_ADynamicElementInACheckerFunction) {
  ExpectDynamicReportedAlone(
      "    function int fn1(); return q[0]; endfunction\n");
}

TEST(CheckerEnclosingReference, DISABLED_ADynamicElementInACovergroup) {
  ExpectDynamicReportedAlone(
      "    covergroup cg @(posedge clk);\n      cp: coverpoint q[0];\n"
      "    endgroup\n    cg cgi = new();\n");
  ExpectDynamicReportedAlone(
      "    covergroup cg @(q[0]);\n      cp: coverpoint clk;\n"
      "    endgroup\n    cg cgi = new();\n");
}

TEST(CheckerEnclosingReference, DISABLED_ADynamicElementInADefaultDisableIff) {
  ExpectDynamicReportedAlone("    default disable iff q[0];\n");
}

TEST(CheckerEnclosingReference, DISABLED_ADynamicElementInEachActionBranch) {
  std::string src = InModuleChecker(
      "    a5: assert property (@(posedge clk) 1)\n"
      "      $display(\"%0d\", q[0]);\n"
      "    else\n"
      "      $display(\"%0d\", q[1]);\n");
  ElabFixture f;
  ElaborateSrc(src, f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), DynamicReport("q"),
                            LineHolding(src, "q[0]"), "17.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), DynamicReport("q"),
                            LineHolding(src, "q[1]"), "17.2"));
  EXPECT_EQ(ErrorCount(f), 2u);
}

const char* const kCheckerGenerateBlocks[][2] = {
    {"    if (1) begin : g\n", "    end\n"},
    {"    for (genvar i = 0; i < 1; i++) begin : g\n", "    end\n"},
    {"    case (1) 1: begin : g\n", "    end endcase\n"},
};

TEST(CheckerEnclosingReference, DISABLED_EachKindInACheckersGenerateBlock) {
  for (const auto& block : kCheckerGenerateBlocks) {
    ExpectReportedAlone(
        InModuleChecker(std::string(block[0]) +
                        "      a2: assert property (@(posedge clk) q[0] == "
                        "1);\n" +
                        block[1]),
        DynamicReport("q"), "q[0]");
    ExpectReportedAlone(
        InModuleChecker(std::string(block[0]) +
                        "      a2: assert property (@(posedge clk) fa.v == "
                        "1);\n" +
                        block[1]),
        ForkReport("fa"), "fa.v");
  }
}

struct EnclosingPlace {
  const char* name;
  const char* open;
  const char* close;
  const char* instance;
};

const char* const kPlaceDeclarations =
    "  logic clk;\n"
    "  int q[$];\n"
    "  initial fork : fa int v; join\n"
    "  task automatic t; int y; endtask\n";

const EnclosingPlace kProceduralPlaces[] = {
    {"interface", "interface ifc;\n", "endinterface\n", "  ifc i();\n"},
    {"program", "program prg;\n", "endprogram\n", "  prg p();\n"},
};

std::string InPlace(const EnclosingPlace& place, const std::string& item) {
  return std::string(place.open) + kPlaceDeclarations +
         "  checker c;\n    a1: assert property (@(posedge clk) " + item +
         " == 1);\n  endchecker\n  c u();\n" + place.close + "module m;\n" +
         place.instance + "endmodule\n";
}

TEST(CheckerEnclosingReference, DISABLED_EachKindInAnInterfaceAndAProgram) {
  for (const auto& place : kProceduralPlaces) {
    SCOPED_TRACE(place.name);
    ExpectReportedAlone(InPlace(place, "q[0]"), DynamicReport("q"), "q[0]");
    ExpectReportedAlone(InPlace(place, "fa.v"), ForkReport("fa"), "fa.v");
    ExpectReportedAlone(InPlace(place, "t.y"), AutomaticReport("y"), "t.y");
  }
}

TEST(CheckerEnclosingReference, DISABLED_AnAutomaticVariableOfAnOuterChecker) {
  ExpectReportedAlone(
      "checker o(logic clk);\n"
      "  function automatic int fo(); int y; return y; endfunction\n"
      "  checker c;\n"
      "    a1: assert property (@(posedge clk) fo.y == 1);\n"
      "  endchecker\n"
      "  c u();\n"
      "endchecker\n"
      "module m;\n"
      "  logic clk;\n"
      "  o uo(clk);\n"
      "endmodule\n",
      AutomaticReport("y"), "fo.y");
}

const char* const kStaticScopeDeclarations =
    "  logic clk;\n"
    "  int q[$];\n"
    "  function automatic int fu(); int y; return y; endfunction\n"
    "  checker c;\n"
    "    a1: assert property (@(posedge clk) REF == 1);\n"
    "  endchecker\n";

std::string WithRef(const std::string& text, const std::string& ref) {
  std::string out = text;
  out.replace(out.find("REF"), 3, ref);
  return out;
}

TEST(CheckerEnclosingReference, DISABLED_EachKindInTheCompilationUnit) {
  for (const char* ref : {"q[0]", "fu.y"}) {
    std::string src = WithRef(kStaticScopeDeclarations, ref) +
                      "module m;\n  c u();\nendmodule\n";
    ExpectReportedAlone(
        src,
        std::string(ref) == "q[0]" ? DynamicReport("q") : AutomaticReport("y"),
        ref);
  }
}

TEST(CheckerEnclosingReference, DISABLED_EachKindInAPackage) {
  for (const char* ref : {"q[0]", "fu.y"}) {
    std::string src = "package pk;\n" + WithRef(kStaticScopeDeclarations, ref) +
                      "endpackage\nmodule m;\n  pk::c u();\nendmodule\n";
    ExpectReportedAlone(
        src,
        std::string(ref) == "q[0]" ? DynamicReport("q") : AutomaticReport("y"),
        ref);
  }
}

TEST(CheckerEnclosingReference, DISABLED_EachKindInAGenerateBlock) {
  for (const char* ref : {"q[0]", "fa.v", "t.y"}) {
    std::string src =
        "module m;\n"
        "  logic clk;\n"
        "  int q[$];\n"
        "  initial fork : fa int v; join\n"
        "  task automatic t; int y; endtask\n"
        "  if (1) begin : g\n"
        "    checker c;\n"
        "      a1: assert property (@(posedge clk) " +
        std::string(ref) +
        " == 1);\n"
        "    endchecker\n"
        "    c u();\n"
        "  end\n"
        "endmodule\n";
    std::string r = std::string(ref);
    ExpectReportedAlone(src,
                        r == "q[0]"   ? DynamicReport("q")
                        : r == "fa.v" ? ForkReport("fa")
                                      : AutomaticReport("y"),
                        ref);
  }
}

TEST(CheckerEnclosingReference, AFormalOrVariableNamedLikeItIsAccepted) {
  ExpectAccepted(
      "module m;\n"
      "  logic clk;\n"
      "  int q[$];\n"
      "  checker c(logic [3:0] q);\n"
      "    a1: assert property (@(posedge clk) q[0] == 1);\n"
      "  endchecker\n"
      "  checker d;\n"
      "    bit [3:0] q;\n"
      "    a1: assert property (@(posedge clk) q[0] == 1);\n"
      "  endchecker\n"
      "  logic [3:0] w;\n"
      "  c u(w);\n"
      "  d ud();\n"
      "endmodule\n");
}

const char* const kNoLeadingClock =
    "concurrent assertion has no leading clocking event";

std::string UnclockedCheckerIn(const std::string& open,
                               const std::string& close,
                               const std::string& own) {
  return open + "  checker cu(logic clk, logic x);\n" + own +
         "    a1: assert property (x);\n"
         "  endchecker\n" +
         close;
}

std::string InstantiatingModule(const std::string& name) {
  return "module m;\n"
         "  logic clk = 0, a = 0;\n"
         "  default clocking @(posedge clk); endclocking\n"
         "  " +
         name + " u(clk, a);\nendmodule\n";
}

TEST(CheckerInheritedDefaults, AUnitCheckerTakesNoModuleClocking) {
  std::string src = UnclockedCheckerIn("", "", "") + InstantiatingModule("cu");
  ElabFixture f;
  ElaborateSrc(src, f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoLeadingClock,
                            LineHolding(src, "a1:"), "16.16"));
}

TEST(CheckerInheritedDefaults, AUnitCheckerWithItsOwnClockingIsAccepted) {
  ExpectAccepted(
      UnclockedCheckerIn("", "",
                         "    default clocking @(posedge clk); endclocking\n") +
      InstantiatingModule("cu"));
}

TEST(CheckerInheritedDefaults, APackageCheckerTakesNoModuleClocking) {
  std::string src = UnclockedCheckerIn("package pk;\n", "endpackage\n", "") +
                    InstantiatingModule("pk::cu");
  ElabFixture f;
  ElaborateSrc(src, f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoLeadingClock,
                            LineHolding(src, "a1:"), "16.16"));
}

TEST(CheckerInheritedDefaults, APackageCheckerWithItsOwnClockingIsAccepted) {
  ExpectAccepted(
      UnclockedCheckerIn("package pk;\n", "endpackage\n",
                         "    default clocking @(posedge clk); endclocking\n") +
      InstantiatingModule("pk::cu"));
}

const char* const kTypeNotDeclared =
    "declaration of type 't_b' does not precede";

std::string Unresolved(const std::string& name) {
  return "reference to unresolved identifier '" + name + "'";
}

void ExpectReportedUnder(const std::string& src, const std::string& report,
                         const std::string& at, const char* subclause) {
  ElabFixture f;
  ElaborateSrc(src, f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), report, LineHolding(src, at),
                            subclause))
      << src;
}

const char* const kLocalChecker =
    "  checker chk;\n"
    "    typedef logic [7:0] t_b;\n"
    "    typedef enum logic [1:0] {E0, E1, E2} e_t;\n"
    "    t_b own;\n"
    "    e_t own_e = E2;\n"
    "    int v;\n"
    "    rand bit fr;\n"
    "  endchecker\n";

std::string ModuleWithLocalChecker(const std::string& after) {
  return std::string("module m;\n") + kLocalChecker + "  chk u();\n" + after +
         "endmodule\n";
}

TEST(CheckerLocalDeclarations, ItsTypedefIsNoTypeOutside) {
  ExpectReportedUnder(ModuleWithLocalChecker("  t_b w;\n"), kTypeNotDeclared,
                      "t_b w;", "6.18");
}

TEST(CheckerLocalDeclarations, ItsOwnUsesOfItsDeclarationsAreAccepted) {
  ExpectAccepted(ModuleWithLocalChecker(""));
}

TEST(CheckerLocalDeclarations, ItsEnumConstantIsUnknownOutside) {
  ExpectReportedUnder(ModuleWithLocalChecker("  int r;\n  initial r = E1;\n"),
                      Unresolved("E1"), "r = E1", "23.9");
}

TEST(CheckerLocalDeclarations, ItsVariableIsUnknownOutside) {
  ExpectReportedUnder(ModuleWithLocalChecker("  int r;\n  initial r = v;\n"),
                      Unresolved("v"), "r = v", "23.9");
}

TEST(CheckerLocalDeclarations, ItsFreeVariableIsUnknownOutside) {
  ExpectReportedUnder(ModuleWithLocalChecker("  int r;\n  initial r = fr;\n"),
                      Unresolved("fr"), "r = fr", "23.9");
}

TEST(CheckerLocalDeclarations, TheModulesOwnVariableIsAccepted) {
  ExpectAccepted(
      ModuleWithLocalChecker("  int r, mine;\n  initial r = mine;\n"));
}

TEST(CheckerLocalDeclarations,
     AnotherCheckerSeesNeitherItsTypedefNorItsVariable) {
  ExpectReportedUnder(
      ModuleWithLocalChecker("  checker other;\n    t_b w;\n  endchecker\n"
                             "  other uo();\n"),
      kTypeNotDeclared, "t_b w;", "6.18");
  ExpectReportedUnder(
      ModuleWithLocalChecker("  logic clk;\n  checker other;\n"
                             "    a1: assert property (@(posedge clk) v == "
                             "0);\n  endchecker\n  other uo();\n"),
      Unresolved("v"), "v == 0", "23.9");
}

TEST(CheckerLocalDeclarations, AnotherCheckerDeclaringTheNameItselfIsAccepted) {
  ExpectAccepted(ModuleWithLocalChecker(
      "  checker other;\n    typedef logic [3:0] t_b;\n    t_b w;\n"
      "    int v;\n  endchecker\n  other uo();\n"));
}

TEST(CheckerLocalDeclarations, ANestedCheckerSeesItsOuterCheckersNames) {
  ExpectAccepted(
      "module m;\n"
      "  logic clk;\n"
      "  checker outer;\n"
      "    typedef logic [7:0] t_b;\n"
      "    int v;\n"
      "    checker inner;\n"
      "      t_b w;\n"
      "      a1: assert property (@(posedge clk) v == 0);\n"
      "    endchecker\n"
      "    inner ui();\n"
      "  endchecker\n"
      "  outer uo();\n"
      "endmodule\n");
}

struct LocalPlace {
  const char* name;
  const char* before;
  const char* open;
  const char* close;
};

const LocalPlace kLocalPlaces[] = {
    {"interface", "", "interface ifc;\n",
     "endinterface\nmodule m; ifc i(); endmodule\n"},
    {"program", "", "program prg;\n",
     "endprogram\nmodule m; prg p(); endmodule\n"},
    {"generate block", "", "module m;\n  if (1) begin : g\n",
     "  end\nendmodule\n"},
    {"checker", "", "checker o;\n",
     "endchecker\nmodule m; o uo(); endmodule\n"},
};

TEST(CheckerLocalDeclarations, ItsTypedefIsNoTypeOutsideWhereverDeclared) {
  for (const auto& place : kLocalPlaces) {
    SCOPED_TRACE(place.name);
    std::string src = std::string(place.open) +
                      "  checker chk;\n    typedef logic [7:0] t_b;\n"
                      "  endchecker\n  t_b w;\n" +
                      place.close;
    ExpectReportedUnder(src, kTypeNotDeclared, "t_b w;", "6.18");
  }
}

TEST(CheckerLocalDeclarations,
     DISABLED_APackageCheckersTypedefIsNoTypeInThePackage) {
  ExpectReportedUnder(
      "package pk;\n  checker chk;\n    typedef logic [7:0] t_b;\n"
      "  endchecker\n  t_b w;\nendpackage\nmodule m; endmodule\n",
      kTypeNotDeclared, "t_b w;", "6.18");
}

TEST(CheckerLocalDeclarations, AUnitCheckersTypedefIsNoTypeInAModule) {
  ExpectReportedUnder(
      "checker chk;\n  typedef logic [7:0] t_b;\nendchecker\n"
      "module m;\n  t_b w;\nendmodule\n",
      kTypeNotDeclared, "t_b w;", "6.18");
}

TEST(CheckerLocalDeclarations, APackageCheckersTypedefIsNoTypeForAnImporter) {
  ExpectReportedUnder(
      "package pk;\n  checker chk;\n    typedef logic [7:0] t_b;\n"
      "  endchecker\nendpackage\n"
      "module m;\n  import pk::*;\n  t_b w;\nendmodule\n",
      kTypeNotDeclared, "t_b w;", "6.18");
}

}  // namespace
