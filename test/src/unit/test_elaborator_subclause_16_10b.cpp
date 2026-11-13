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

}  // namespace
