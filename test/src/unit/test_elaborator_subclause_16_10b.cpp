#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <iterator>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

std::string Hidden(const char* kind, const char* owner,
                   const char* local = "v") {
  return std::string("'") + local + "' is a local variable of " + kind + " '" +
         owner + "' and is not visible outside its body";
}

std::string InModule(const std::string& item) {
  return "module m;\n"
         "  logic clk, a, b;\n"
         "  int w;\n"
         "  sequence ss; int v; @(posedge clk) (a, v = 1); endsequence\n"
         "  sequence sl(lv); @(posedge clk) (a, lv = 1); endsequence\n"
         "  property pp; int v; @(posedge clk) (a, v = 1) ##1 b; endproperty\n"
         "  property pe(); int v; @(posedge clk) (a, v = 1) ##1 b;"
         " endproperty\n"
         "  sequence sf(local input int f); @(posedge clk) a ##1 (f == 1);"
         " endsequence\n"
         "  sequence mid; ss ##1 a; endsequence\n"
         "  " +
         item + "\nendmodule\n";
}

struct VisibilityCase {
  std::string bad;
  std::string good;
  const char* at;
  std::string message;
  const char* subclause;
};

VisibilityCase Sequence(const std::string& bad, const std::string& good,
                        const char* at) {
  return {bad, good, at, Hidden("sequence", "ss"), "16.10"};
}

void ExpectEachCase(const VisibilityCase* cases, size_t count) {
  for (size_t i = 0; i < count; ++i) {
    const VisibilityCase& c = cases[i];
    {
      SCOPED_TRACE(c.bad);
      ElabFixture f;
      ElaborateSrc(c.bad, f);
      uint32_t line = LineHolding(c.bad, c.at);
      ASSERT_NE(line, 0u);
      EXPECT_TRUE(
          ReportedError(f.diag.Diagnostics(), c.message, line, c.subclause));
    }
    SCOPED_TRACE(c.good);
    ElabFixture g;
    ElaborateSrc(c.good, g);
    EXPECT_FALSE(g.diag.HasErrors());
  }
}

TEST(InstanceLocalVisibility, AReadInAnInstantiatingDeclarationIsReported) {
  const VisibilityCase kCases[] = {
      Sequence(InModule("sequence t; ss ##1 (b == v); endsequence"),
               InModule("sequence t; int v; sl(v) ##1 (b == v); endsequence"),
               "(b == v)"),
      Sequence(InModule("property q; ss |-> (b == v); endproperty"),
               InModule("property q; int v; sl(v) |-> (b == v); endproperty"),
               "(b == v)"),
      {InModule("property q; pp and (b == v); endproperty"),
       InModule("property q; int v; pp and (sl(v) ##1 (b == v));"
                " endproperty"),
       "(b == v)", Hidden("property", "pp"), "16.10"},
      {InModule("property q; pe() and (b == v); endproperty"),
       InModule("property q; int v; pe() and (sl(v) ##1 (b == v));"
                " endproperty"),
       "(b == v)", Hidden("property", "pe"), "16.10"},
  };
  ExpectEachCase(kCases, std::size(kCases));
}

TEST(InstanceLocalVisibility, AReadInAnInstantiatingStatementIsReported) {
  const VisibilityCase kCases[] = {
      Sequence(InModule("assert property (@(posedge clk) ss ##1 (b == v));"),
               InModule("assert property (@(posedge clk) ss ##1 (b == w));"),
               "(b == v)"),
      Sequence(InModule("assume property (@(posedge clk) ss ##1 (b == v));"),
               InModule("assume property (@(posedge clk) ss ##1 (b == w));"),
               "(b == v)"),
      Sequence(InModule("cover property (@(posedge clk) ss ##1 (b == v));"),
               InModule("cover property (@(posedge clk) ss ##1 (b == w));"),
               "(b == v)"),
      Sequence(InModule("cover sequence (@(posedge clk) ss ##1 (b == v));"),
               InModule("cover sequence (@(posedge clk) ss ##1 (b == w));"),
               "(b == v)"),
      Sequence(InModule("restrict property (@(posedge clk) ss ##1 (b == v));"),
               InModule("restrict property (@(posedge clk) ss ##1 (b == w));"),
               "(b == v)"),
      {InModule("assert property (@(posedge clk) pp and (b == v));"),
       InModule("assert property (@(posedge clk) pp and (b == w));"),
       "(b == v)", Hidden("property", "pp"), "16.10"},
  };
  ExpectEachCase(kCases, std::size(kCases));
}

TEST(InstanceLocalVisibility, ALocalFormalOrANestedInstancesLocalIsUnresolved) {
  const VisibilityCase kCases[] = {
      {InModule("assert property (@(posedge clk) sf(1) ##1 (b == f));"),
       InModule("assert property (@(posedge clk) sf(1) ##1 (b == w));"),
       "(b == f)", "reference to unresolved identifier 'f'", "23.9"},
      {InModule("assert property (@(posedge clk) mid ##1 (b == v));"),
       InModule("assert property (@(posedge clk) mid ##1 (b == w));"),
       "(b == v)", "reference to unresolved identifier 'v'", "23.9"},
  };
  ExpectEachCase(kCases, std::size(kCases));
}

std::string InElement(const std::string& element, const std::string& read) {
  std::string head;
  std::string tail;
  std::string use;
  if (element == "interface") {
    head = "interface e(input logic clk, a, b);\n";
    tail = "endinterface\n";
    use = "  e e1(clk, a, b);\n";
  } else if (element == "program") {
    head = "program e(input logic clk, a, b);\n";
    tail = "endprogram\n";
    use = "  e e1(clk, a, b);\n";
  } else {
    head = "checker e(logic clk, logic a, logic b);\n";
    tail = "endchecker\n";
    use = "  e e1(clk, a, b);\n";
  }
  return head +
         "  sequence ss; int v; @(posedge clk) (a, v = 1); endsequence\n"
         "  sequence sl(lv); @(posedge clk) (a, lv = 1); endsequence\n"
         "  " +
         read + "\n" + tail + "module m;\n  logic clk, a, b;\n" + use +
         "endmodule\n";
}

TEST(InstanceLocalVisibility, AReadInEachOtherDesignElementIsReported) {
  for (const char* element : {"interface", "program", "checker"}) {
    const VisibilityCase kCases[] = {
        Sequence(
            InElement(element,
                      "a1: assert property (@(posedge clk) ss ##1 (b == v));"),
            InElement(element,
                      "a1: assert property (@(posedge clk) ss ##1 b);"),
            "(b == v)"),
        Sequence(
            InElement(element, "sequence t; ss ##1 (b == v); endsequence"),
            InElement(element,
                      "sequence t; int v; sl(v) ##1 (b == v); endsequence"),
            "(b == v)"),
    };
    ExpectEachCase(kCases, std::size(kCases));
  }
}

TEST(InstanceLocalVisibility,
     DISABLED_AReadInAProceduralAssertionOrAnExpectIsReported) {
  const VisibilityCase kCases[] = {
      Sequence(
          InModule("always @(posedge clk) assert property (ss ##1 (b == v));"),
          InModule("always @(posedge clk) assert property (ss ##1 (b == w));"),
          "(b == v)"),
      Sequence(
          InModule("initial assert property (@(posedge clk) ss ##1 (b == v));"),
          InModule("initial assert property (@(posedge clk) ss ##1 (b == w));"),
          "(b == v)"),
      Sequence(InModule("initial expect (@(posedge clk) ss ##1 (b == v));"),
               InModule("initial expect (@(posedge clk) ss ##1 (b == w));"),
               "(b == v)"),
  };
  ExpectEachCase(kCases, std::size(kCases));
}

TEST(InstanceLocalVisibility, DISABLED_AReadInAGenerateBlockIsReported) {
  const VisibilityCase kCases[] = {
      Sequence(
          InModule("if (1) begin : g\n"
                   "    assert property (@(posedge clk) ss ##1 (b == v));\n"
                   "  end"),
          InModule("if (1) begin : g\n"
                   "    assert property (@(posedge clk) ss ##1 (b == w));\n"
                   "  end"),
          "(b == v)"),
      {InModule("if (1) begin : g\n"
                "    sequence gs; int v; @(posedge clk) (a, v = 1);"
                " endsequence\n"
                "    assert property (@(posedge clk) gs ##1 (b == v));\n"
                "  end"),
       InModule("if (1) begin : g\n"
                "    sequence gs; int v; @(posedge clk) (a, v = 1);"
                " endsequence\n"
                "    assert property (@(posedge clk) gs ##1 (b == w));\n"
                "  end"),
       "(b == v)", Hidden("sequence", "gs"), "16.10"},
  };
  ExpectEachCase(kCases, std::size(kCases));
}

std::string OutsideModules(const std::string& head, const std::string& tail,
                           const std::string& read) {
  return head +
         "  sequence os; int v; (1, v = 1); endsequence\n"
         "  sequence ol(lv); (1, lv = 1); endsequence\n"
         "  " +
         read + "\n" + tail + "module m;\nendmodule\n";
}

TEST(InstanceLocalVisibility,
     DISABLED_AReadInAPackageOrTheCompilationUnitIsReported) {
  const std::string kPackageHead = "package pk;\n";
  const std::string kPackageTail = "endpackage\n";
  const VisibilityCase kCases[] = {
      {OutsideModules(kPackageHead, kPackageTail,
                      "property q; os ##1 (v == 1); endproperty"),
       OutsideModules(kPackageHead, kPackageTail,
                      "property q; int v; ol(v) ##1 (v == 1); endproperty"),
       "(v == 1); endproperty", Hidden("sequence", "os"), "16.10"},
      {OutsideModules(kPackageHead, kPackageTail,
                      "sequence t; os ##1 (v == 1); endsequence"),
       OutsideModules(kPackageHead, kPackageTail,
                      "sequence t; int v; ol(v) ##1 (v == 1); endsequence"),
       "(v == 1); endsequence", Hidden("sequence", "os"), "16.10"},
      {OutsideModules("", "", "property q; os ##1 (v == 1); endproperty"),
       OutsideModules("", "",
                      "property q; int v; ol(v) ##1 (v == 1); endproperty"),
       "(v == 1); endproperty", Hidden("sequence", "os"), "16.10"},
      {OutsideModules("", "", "sequence t; os ##1 (v == 1); endsequence"),
       OutsideModules("", "",
                      "sequence t; int v; ol(v) ##1 (v == 1); endsequence"),
       "(v == 1); endsequence", Hidden("sequence", "os"), "16.10"},
  };
  ExpectEachCase(kCases, std::size(kCases));
}

TEST(InstanceLocalVisibility, AnOwnLocalOfTheSameNameIsAccepted) {
  for (const char* item :
       {"sequence t; int v; ss ##1 (a, v = 2) ##1 (b == v); endsequence",
        "property q; int v; (ss ##1 (a, v = 2)) |-> (b == v); endproperty",
        "property q; int v; (a, v = 2) ##1 pp ##1 (b == v); endproperty"}) {
    SCOPED_TRACE(item);
    ElabFixture f;
    ElaborateSrc(InModule(item), f);
    EXPECT_FALSE(f.diag.HasErrors());
  }
}

constexpr const char* kWholeActual =
    "a local variable passed to an instance whose sequence assigns the "
    "formal shall be an entire actual argument";

constexpr const char* kAssigningSequences =
    "  sequence sub(lv); (a, lv = d) ##1 (b == lv); endsequence\n"
    "  sequence sp(lv); (a, lv += d) ##1 (b == lv); endsequence\n"
    "  sequence si(lv); (a, lv++) ##1 (b == lv); endsequence\n"
    "  sequence sr(lv); a ##1 (b == lv); endsequence\n";

std::string TopSequence(const std::string& instance,
                        const std::string& name = "top") {
  return "  sequence " + name + "; int v1; (c, v1 = 0) ##1 " + instance +
         " ##1 (b == v1); endsequence\n";
}

std::string AssigningModule(const std::string& body) {
  return std::string(
             "module m;\n"
             "  logic clk, a, b, c;\n"
             "  int d;\n"
             "  default clocking @(posedge clk); endclocking\n") +
         kAssigningSequences + body + "endmodule\n";
}

void ExpectWholeActualReported(const std::string& bad, const char* at,
                               const std::string& good) {
  {
    SCOPED_TRACE(bad);
    ElabFixture f;
    ElaborateSrc(bad, f);
    uint32_t line = LineHolding(bad, at);
    ASSERT_NE(line, 0u);
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kWholeActual, line, "16.10"));
  }
  SCOPED_TRACE(good);
  ElabFixture g;
  ElaborateSrc(good, g);
  EXPECT_FALSE(g.diag.HasErrors());
}

struct ActualPair {
  const char* bad;
  const char* good;
};

TEST(WholeLocalActual, DISABLED_ALocalInsideAnAssignedFormalsActualIsReported) {
  const ActualPair kPairs[] = {
      {"sub(v1 + 1)", "sub(v1)"},      {"sp(v1 + 1)", "sp(v1)"},
      {"si(v1 + 1)", "si(v1)"},        {"sub(v1[3:0])", "sub(v1)"},
      {"sub(v1[0])", "sub(v1)"},       {"sub({v1})", "sub(v1)"},
      {"sub(c ? v1 : v1)", "sub(v1)"}, {"sub(.lv(v1 + 1))", "sub(.lv(v1))"},
  };
  for (const ActualPair& pair : kPairs) {
    ExpectWholeActualReported(AssigningModule(TopSequence(pair.bad)), pair.bad,
                              AssigningModule(TopSequence(pair.good)));
  }
}

TEST(WholeLocalActual, DISABLED_ALocalInsideAnActualInAPropertyIsReported) {
  ExpectWholeActualReported(
      AssigningModule("  property q; int v1;"
                      " (c, v1 = 0) ##1 sub(v1 + 1) |-> (b == v1);"
                      " endproperty\n"),
      "sub(v1 + 1)",
      AssigningModule("  property q; int v1;"
                      " (c, v1 = 0) ##1 sub(v1) |-> (b == v1);"
                      " endproperty\n"));
}

TEST(WholeLocalActual, ALocalInsideAReadOnlyFormalsActualIsAccepted) {
  ElabFixture f;
  ElaborateSrc(AssigningModule(TopSequence("sr(v1 + 1)") +
                               TopSequence("sr(v1[3:0])", "top2")),
               f);
  EXPECT_FALSE(f.diag.HasErrors());
}

std::string AssigningPlace(const std::string& place,
                           const std::string& instance) {
  std::string body = std::string(kAssigningSequences) + TopSequence(instance);
  if (place == "interface") {
    return "interface e(input logic clk, a, b, c);\n  int d;\n" + body +
           "endinterface\n";
  }
  if (place == "program") {
    return "program e(input logic clk, a, b, c);\n  int d;\n" + body +
           "endprogram\n";
  }
  if (place == "checker") {
    return "checker e(logic clk, logic a, logic b, logic c, int d);\n" + body +
           "endchecker\n";
  }
  if (place == "package") {
    return "package e;\n  logic a, b, c;\n  int d;\n" + body + "endpackage\n";
  }
  if (place == "unit") {
    return "logic a, b, c;\nint d;\n" + body + "module m;\nendmodule\n";
  }
  if (place == "generate") {
    return "module m;\n  logic clk, a, b, c;\n  int d;\n"
           "  if (1) begin : g\n" +
           body + "  end\nendmodule\n";
  }
  return "module m;\n  logic clk, a, b, c;\n  int d;\n"
         "  clocking cb @(posedge clk);\n" +
         body + "  endclocking\nendmodule\n";
}

TEST(WholeLocalActual, DISABLED_ALocalInsideAnActualIsReportedInEveryPlace) {
  for (const char* place : {"interface", "program", "checker", "package",
                            "unit", "generate", "clocking"}) {
    SCOPED_TRACE(place);
    ExpectWholeActualReported(AssigningPlace(place, "sub(v1 + 1)"),
                              "sub(v1 + 1)", AssigningPlace(place, "sub(v1)"));
  }
}

constexpr const char* kUnassignedV1 =
    "the local variable 'v1' is referenced at a point where it is unassigned";

constexpr const char* kTriggeredSequences =
    "  sequence sub(lv); (a, lv = d); endsequence\n"
    "  sequence sub_or(lv); ((a, lv = d) or b); endsequence\n"
    "  sequence sub_both(lv); ((a, lv = d) or (b, lv = 1)); endsequence\n";

std::string TriggeredBody(const std::string& before, const std::string& app,
                          bool read) {
  std::string body = "  sequence t; int v1;\n    " + before + app;
  if (read) body += "\n    ##1 (b == v1)";
  return body + ";\n  endsequence\n";
}

std::string TriggeredPlace(const std::string& place, const std::string& body) {
  std::string decls = std::string(kTriggeredSequences) + body;
  const std::string kUser =
      "module m;\n  logic clk, a, b, c;\n  int d;\n  e e1(clk, a, b, c";
  if (place == "module") {
    return "module m;\n  logic clk, a, b, c;\n  int d;\n" + decls +
           "endmodule\n";
  }
  if (place == "interface") {
    return "interface e(input logic clk, a, b, c);\n  int d;\n" + decls +
           "endinterface\n" + kUser + ");\nendmodule\n";
  }
  if (place == "program") {
    return "program e(input logic clk, a, b, c);\n  int d;\n" + decls +
           "endprogram\n" + kUser + ");\nendmodule\n";
  }
  if (place == "checker") {
    return "checker e(logic clk, logic a, logic b, logic c, int d);\n" + decls +
           "endchecker\n" + kUser + ", d);\nendmodule\n";
  }
  return "package e;\n  logic a, b, c;\n  int d;\n" + decls +
         "endpackage\nmodule m;\n  import e::*;\nendmodule\n";
}

const char* const kNotMaximal[] = {
    "!sub(v1).triggered",          "(sub(v1).triggered && b)",
    "(sub(v1).triggered || b)",    "(sub(v1).triggered ? b : c)",
    "(c ? sub(v1).triggered : b)", "(c ? b : sub(v1).triggered)",
    "(sub(v1).triggered == b)",    "sub_or(v1).triggered",
};

const char* const kFlowingOut[] = {
    "sub(v1).triggered",
    "(sub(v1).triggered)",
};

void ExpectReadReportedAndActualNot(const std::string& src) {
  SCOPED_TRACE(src);
  ElabFixture f;
  ElaborateSrc(src, f);
  uint32_t actual = LineHolding(src, ".triggered");
  uint32_t read = LineHolding(src, "(b == v1)");
  ASSERT_NE(actual, 0u);
  ASSERT_NE(read, 0u);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kUnassignedV1, read, "16.10"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kUnassignedV1, actual, "16.10"));
}

void ExpectAccepted(const std::string& src) {
  SCOPED_TRACE(src);
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(TriggeredLocalFlow, DISABLED_ANonFlowingApplicationReportsOnlyTheRead) {
  for (const char* place :
       {"module", "interface", "program", "checker", "package"}) {
    for (const char* app : kNotMaximal) {
      ExpectReadReportedAndActualNot(
          TriggeredPlace(place, TriggeredBody("c ##1 ", app, true)));
    }
  }
}

TEST(TriggeredLocalFlow,
     DISABLED_ANonFlowingApplicationReadByNothingIsAccepted) {
  for (const char* place :
       {"module", "interface", "program", "checker", "package"}) {
    for (const char* app : kNotMaximal) {
      ExpectAccepted(
          TriggeredPlace(place, TriggeredBody("c ##1 ", app, false)));
    }
  }
}

TEST(TriggeredLocalFlow, AFlowingApplicationIsReadAfterward) {
  for (const char* place :
       {"module", "interface", "program", "checker", "package"}) {
    for (const char* app : kFlowingOut) {
      ExpectAccepted(TriggeredPlace(place, TriggeredBody("c ##1 ", app, true)));
    }
  }
}

TEST(TriggeredLocalFlow, DISABLED_AFormalAssignedInBothOperandsOfAnOrFlowsOut) {
  for (const char* place :
       {"module", "interface", "program", "checker", "package"}) {
    ExpectAccepted(TriggeredPlace(
        place, TriggeredBody("c ##1 ", "sub_both(v1).triggered", true)));
  }
}

TEST(TriggeredLocalFlow, ALocalAssignedBeforeIsReadAfterAnyApplication) {
  for (const char* place :
       {"module", "interface", "program", "checker", "package"}) {
    for (const char* app : kNotMaximal) {
      ExpectAccepted(
          TriggeredPlace(place, TriggeredBody("(c, v1 = 0) ##1 ", app, true)));
    }
  }
}

TEST(TriggeredLocalFlow, DISABLED_AnAntecedentApplicationReportsOnlyTheRead) {
  ExpectReadReportedAndActualNot(TriggeredPlace("module",
                                                "  property q; int v1;\n"
                                                "    c ##1 !sub(v1).triggered\n"
                                                "    |-> (b == v1);\n"
                                                "  endproperty\n"));
}

TEST(TriggeredLocalFlow, AFlowingOrAssignedAntecedentIsReadInTheConsequent) {
  for (const char* body : {"  property q; int v1;\n"
                           "    c ##1 sub(v1).triggered\n"
                           "    |-> (b == v1);\n"
                           "  endproperty\n",
                           "  property q; int v1;\n"
                           "    (c, v1 = 0) ##1 !sub(v1).triggered\n"
                           "    |-> (b == v1);\n"
                           "  endproperty\n"}) {
    ExpectAccepted(TriggeredPlace("module", body));
  }
}

}  // namespace
