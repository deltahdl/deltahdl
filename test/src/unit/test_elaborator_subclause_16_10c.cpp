#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr const char* kUnassignedX =
    "the local variable 'x' is referenced at a point where it is unassigned";

constexpr const char* kAssigner = "((b, x = d) ##1 c)";
constexpr const char* kReader = "(c ##1 (e == x))";

std::string Filled(std::string text, const std::string& left,
                   const std::string& right) {
  size_t at = text.find("@L");
  text.replace(at, 2, left);
  at = text.find("@R");
  text.replace(at, 2, right);
  return text;
}

std::string SiblingModule(const std::string& decl) {
  return "module m;\n"
         "  logic clk, a, b, c, e;\n"
         "  int d;\n"
         "  default clocking @(posedge clk); endclocking\n"
         "  " +
         decl + "\nendmodule\n";
}

void ExpectSiblingReadReported(const std::string& src) {
  SCOPED_TRACE(src);
  ElabFixture f;
  ElaborateSrc(src, f);
  uint32_t line = LineHolding(src, "(e == x)");
  ASSERT_NE(line, 0u);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kUnassignedX, line, "16.10"));
}

void ExpectAccepted(const std::string& src) {
  SCOPED_TRACE(src);
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
}

void ExpectBothOrdersReported(const std::vector<std::string>& templates,
                              const std::string& assigner = kAssigner,
                              const std::string& reader = kReader) {
  for (const std::string& t : templates) {
    ExpectSiblingReadReported(SiblingModule(Filled(t, assigner, reader)));
    ExpectSiblingReadReported(SiblingModule(Filled(t, reader, assigner)));
  }
}

const char* const kSequenceOperators[] = {"or", "and", "intersect", "within"};

std::vector<std::string> WithEachOperator(const std::string& head,
                                          const std::string& tail,
                                          bool sequence_only_too = true) {
  std::vector<std::string> out;
  for (const char* op : kSequenceOperators) {
    if (!sequence_only_too && std::string(op) != "and" &&
        std::string(op) != "or") {
      continue;
    }
    std::string text = head;
    text += "@L ";
    text += op;
    text += " @R";
    text += tail;
    out.push_back(text);
  }
  return out;
}

TEST(SiblingThreadRead, ASequenceOperandsSiblingReadIsReported) {
  ExpectBothOrdersReported(
      WithEachOperator("sequence s; int x; ", "; endsequence"));
  ExpectBothOrdersReported({
      "sequence s; int x; a ##1 (@L or @R) ##1 c; endsequence",
      "sequence s; int x; ((@L or @R) and a); endsequence",
  });
  ExpectBothOrdersReported({"sequence s; int x; @L or @R; endsequence"},
                           "(a, x = d)", "(b ##0 (e == x))");
}

TEST(SiblingThreadRead, AParenthesizedAntecedentsSiblingReadIsReported) {
  ExpectBothOrdersReported(
      WithEachOperator("property q; int x; (", ") |-> c; endproperty"));
}

TEST(SiblingThreadRead,
     DISABLED_AnUnparenthesizedPropertyAndOrOrsSiblingReadIsReported) {
  std::vector<std::string> templates =
      WithEachOperator("property q; int x; ", " |-> c; endproperty");
  for (const std::string& t :
       WithEachOperator("property q; int x; a |-> ", "; endproperty", false)) {
    templates.push_back(t);
  }
  for (const std::string& t :
       WithEachOperator("property q; int x; a |=> ", "; endproperty", false)) {
    templates.push_back(t);
  }
  for (const std::string& t :
       WithEachOperator("property q; int x; ", "; endproperty", false)) {
    templates.push_back(t);
  }
  ExpectBothOrdersReported(templates);
  ExpectBothOrdersReported(
      WithEachOperator("property q; int x; ", "; endproperty", false),
      "((b, x = d) |-> c)", "(c |-> (e == x))");
}

TEST(SiblingThreadRead, ALocalThatFlowsInOrStaysInItsThreadIsAccepted) {
  for (const char* op : kSequenceOperators) {
    std::string o = op;
    for (const std::string& decl : {
             "sequence s; int x; (a, x = d) ##1 ((b ##1 (e == x)) " + o +
                 " (c ##1 (e == x))); endsequence",
             "sequence s; int x = d; (b ##1 (e == x)) " + o +
                 " (c ##1 (e == x)); endsequence",
             "sequence s; int x; ((b, x = d) ##1 (e == x)) " + o +
                 " ((c, x = 1) ##1 (e == x)); endsequence",
             "sequence s; int x; (a, x = d) ##1 (((b, x = 1) ##1 c) " + o +
                 " (c ##1 (e == x))); endsequence",
         }) {
      ExpectAccepted(SiblingModule(decl));
    }
  }
  for (const char* decl : {
           "property q; int x; ((a, x = d) ##1 b) |-> c ##1 (e == x);"
           " endproperty",
           "sequence s; int x; ((a ##1 (b, x = d)) and (c ##1 e)) ##1"
           " (x == 1); endsequence",
           "sequence s; int x; ((a, x = d) or (b, x = 1)) ##1 (x == 1);"
           " endsequence",
       }) {
    ExpectAccepted(SiblingModule(decl));
  }
}

constexpr const char* kSiblingSequence =
    "sequence s; int x; ((b, x = d) ##1 c) or (c ##1 (e == x)); endsequence";
constexpr const char* kSiblingProperty =
    "property q; int x; (((b, x = d) ##1 c) or (c ##1 (e == x))) |-> c;"
    " endproperty";
constexpr const char* kFlowedSequence =
    "sequence s; int x; (a, x = d) ##1 ((b ##1 (e == x)) or (c ##1"
    " (e == x))); endsequence";

std::string InElement(const std::string& element, const std::string& decl) {
  std::string port_head =
      element == "checker"
          ? "(logic clk, logic a, logic b, logic c,"
            " logic e, int d);\n"
          : "(input logic clk, a, b, c, e, input var int d);\n";
  std::string tail = element == "interface" ? "endinterface\n"
                     : element == "program" ? "endprogram\n"
                                            : "endchecker\n";
  return element + " el" + port_head + "  default clocking @(posedge clk);" +
         " endclocking\n  " + decl + "\n" + tail +
         "module m;\n  logic clk, a, b, c, e;\n  int d;\n"
         "  el u(clk, a, b, c, e, d);\nendmodule\n";
}

TEST(SiblingThreadRead, ASiblingReadInEachOtherDesignElementIsReported) {
  for (const char* element : {"interface", "program", "checker"}) {
    ExpectSiblingReadReported(InElement(element, kSiblingSequence));
    ExpectSiblingReadReported(InElement(element, kSiblingProperty));
    ExpectAccepted(InElement(element, kFlowedSequence));
  }
}

std::string WithFormals(std::string decl) {
  size_t at = decl.find(';');
  decl.insert(at, "(a, b, c, d, e)");
  return decl;
}

std::string InOuterScope(const std::string& place, const std::string& decl) {
  const std::string kModuleHead =
      "module m;\n  logic clk, a, b, c, e;\n  int d;\n";
  const std::string kUse =
      "  cover property (@(posedge clk) @N(a, b, c, d, e));\nendmodule\n";
  std::string name = decl.substr(0, 8) == "sequence" ? "s" : "q";
  auto use = [&](const std::string& prefix) {
    std::string u = kUse;
    u.replace(u.find("@N"), 2, prefix + name);
    return u;
  };
  if (place == "package") {
    return "package pk;\n  " + WithFormals(decl) + "\nendpackage\n" +
           kModuleHead + use("pk::");
  }
  if (place == "import") {
    return "package pk;\n  " + WithFormals(decl) + "\nendpackage\n" +
           kModuleHead + "  import pk::*;\n" + use("");
  }
  if (place == "unit") {
    return WithFormals(decl) + "\n" + kModuleHead + use("");
  }
  if (place == "if") {
    return kModuleHead +
           "  default clocking @(posedge clk); endclocking\n"
           "  if (1) begin : g\n    " +
           decl + "\n  end\nendmodule\n";
  }
  if (place == "for") {
    return kModuleHead +
           "  default clocking @(posedge clk); endclocking\n"
           "  for (genvar k = 0; k < 1; k++) begin : g\n    " +
           decl + "\n  end\nendmodule\n";
  }
  return kModuleHead + "  clocking cb @(posedge clk);\n    " + decl +
         "\n  endclocking\n  cover property (cb." + name + ");\nendmodule\n";
}

TEST(SiblingThreadRead, DISABLED_ASiblingReadInEachOuterScopeIsReported) {
  for (const char* place :
       {"package", "import", "unit", "if", "for", "clocking"}) {
    SCOPED_TRACE(place);
    ExpectSiblingReadReported(InOuterScope(place, kSiblingSequence));
    ExpectSiblingReadReported(InOuterScope(place, kSiblingProperty));
  }
}

TEST(SiblingThreadRead, AFlowedLocalInEachOuterScopeIsAccepted) {
  for (const char* place :
       {"package", "import", "unit", "if", "for", "clocking"}) {
    SCOPED_TRACE(place);
    ExpectAccepted(InOuterScope(place, kFlowedSequence));
  }
}

constexpr const char* kUnassignedY =
    "the local variable 'y' is referenced at a point where it is unassigned";

constexpr const char* kOrInstances =
    "sequence sa(lv); (a, lv = d); endsequence\n"
    "  sequence sb(lv); (b, lv = 1); endsequence\n  ";

void ExpectReadAfterOrReported(const std::string& src) {
  SCOPED_TRACE(src);
  ElabFixture f;
  ElaborateSrc(src, f);
  uint32_t line = LineHolding(src, "(c == y)");
  ASSERT_NE(line, 0u);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kUnassignedY, line, "16.10"));
}

TEST(OrFlowOut, ALocalAssignedInOneOperandIsUnassignedAfterTheOr) {
  for (const char* decl : {
           "sequence s; int y; ((a, y = d) or b) ##1 (c == y); endsequence",
           "sequence s; int y; (b or (a, y = d)) ##1 (c == y); endsequence",
           "sequence s; int y; a ##1 ((b, y = d) or c) ##1 (c == y);"
           " endsequence",
           "sequence s; int y; (((a, y = d) or b) or (c, y = 1)) ##1"
           " (c == y); endsequence",
           "property q; int y; ((a, y = d) or b) |-> (c == y); endproperty",
           "property q; int y; ((a, y = d) or b) |=> (c == y); endproperty",
       }) {
    ExpectReadAfterOrReported(SiblingModule(decl));
  }
  for (const char* decl : {
           "sequence s; int y; (sa(y) or b) ##1 (c == y); endsequence",
           "property q; int y; (b or sa(y)) |-> (c == y); endproperty",
       }) {
    ExpectReadAfterOrReported(SiblingModule(kOrInstances + std::string(decl)));
  }
}

TEST(OrFlowOut, ALocalAssignedInBothOperandsOrBeforeFlowsOut) {
  for (const char* decl : {
           "sequence s; int y; ((a, y = d) or (b, y = 1)) ##1 (c == y);"
           " endsequence",
           "sequence s; int y; (a, y = 0) ##1 ((b, y = 1) or c) ##1"
           " (c == y); endsequence",
           "sequence s; int y; (((a, y = d) or (b, y = 2)) or (c, y = 1))"
           " ##1 (c == y); endsequence",
           "property q; int y; ((a, y = d) or (b, y = 1)) |-> (c == y);"
           " endproperty",
           "property q; int y; ((a, y = d) or (b, y = 1)) |=> (c == y);"
           " endproperty",
       }) {
    ExpectAccepted(SiblingModule(decl));
  }
  for (const char* decl : {
           "sequence s; int y; (sa(y) or sb(y)) ##1 (c == y); endsequence",
           "property q; int y; (sb(y) or sa(y)) |-> (c == y); endproperty",
       }) {
    ExpectAccepted(SiblingModule(kOrInstances + std::string(decl)));
  }
}

constexpr const char* kOneSidedOr =
    "sequence s; int y; ((a, y = d) or b) ##1 (c == y); endsequence";
constexpr const char* kOneSidedOrProperty =
    "property q; int y; ((a, y = d) or b) |-> (c == y); endproperty";
constexpr const char* kTwoSidedOr =
    "sequence s; int y; ((a, y = d) or (b, y = 1)) ##1 (c == y);"
    " endsequence";

TEST(OrFlowOut, AReadAfterAOneSidedOrInEachOtherDesignElementIsReported) {
  for (const char* element : {"interface", "program", "checker"}) {
    ExpectReadAfterOrReported(InElement(element, kOneSidedOr));
    ExpectReadAfterOrReported(InElement(element, kOneSidedOrProperty));
    ExpectAccepted(InElement(element, kTwoSidedOr));
  }
}

TEST(OrFlowOut, DISABLED_AReadAfterAOneSidedOrInEachOuterScopeIsReported) {
  for (const char* place :
       {"package", "import", "unit", "if", "for", "clocking"}) {
    SCOPED_TRACE(place);
    ExpectReadAfterOrReported(InOuterScope(place, kOneSidedOr));
    ExpectReadAfterOrReported(InOuterScope(place, kOneSidedOrProperty));
  }
}

TEST(OrFlowOut, ATwoSidedOrInEachOuterScopeIsAccepted) {
  for (const char* place :
       {"package", "import", "unit", "if", "for", "clocking"}) {
    SCOPED_TRACE(place);
    ExpectAccepted(InOuterScope(place, kTwoSidedOr));
  }
}

}  // namespace
