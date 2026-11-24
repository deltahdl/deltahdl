#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/property_rewrite.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(PropertyRewrite, UnknownNameNotLegal) {
  PropertyRegistry reg;
  auto fp = reg.Flatten("missing", 0);
  EXPECT_FALSE(fp.legal);
}

TEST(PropertyRewrite, LegalFlattenAcceptsAsTopLevel) {
  PropertyRegistry reg;
  ModuleItem decl;
  decl.kind = ModuleItemKind::kPropertyDecl;
  decl.name = "p";
  reg.Register(&decl);

  auto fp = reg.Flatten("p", 0);
  EXPECT_TRUE(fp.legal);
  EXPECT_EQ(fp.remaining_instances, 0);
  EXPECT_TRUE(PropertyRegistry::IsAcceptableAsTopLevelConcurrent(fp));
}

TEST(PropertyRewrite, ArgArityMismatchSurfacesAsNotLegal) {
  PropertyRegistry reg;
  ModuleItem decl;
  decl.kind = ModuleItemKind::kPropertyDecl;
  decl.name = "p";
  decl.prop_formals = {"a", "b", "c"};
  reg.Register(&decl);

  EXPECT_FALSE(reg.Flatten("p", 0).legal);
  EXPECT_FALSE(reg.Flatten("p", 2).legal);
  EXPECT_TRUE(reg.Flatten("p", 3).legal);
}

TEST(PropertyRewrite, FlattenedFormIllegalMakesSourceIllegalFromSource) {
  ElabFixture f;
  Elaborate(
      "module m(input logic clk, r1, a, b, r2);\n"
      "  property leaf;\n"
      "    @(posedge clk) disable iff (r1) a |-> b;\n"
      "  endproperty\n"
      "  property root;\n"
      "    @(posedge clk) disable iff (r2) leaf();\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "property \"root\" nests disable iff clauses", 5,
                            "16.12"));
}

TEST(PropertyRewrite, FlattenedFormLegalKeepsSourceLegalFromSource) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m(input logic clk, a, b, r2);\n"
      "  property leaf;\n"
      "    @(posedge clk) a |-> b;\n"
      "  endproperty\n"
      "  property root;\n"
      "    @(posedge clk) disable iff (r2) leaf();\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(PropertyRewrite,
     HierarchicalPropertyServesAsTopLevelConcurrentFromSource) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  property leaf;\n"
      "    @(posedge clk) a |-> b;\n"
      "  endproperty\n"
      "  property root;\n"
      "    @(posedge clk) leaf();\n"
      "  endproperty\n"
      "  assert property (root);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(PropertyRewrite,
     FlattenedFormNestsDisableIffThroughChainedInstancesFromSource) {
  ElabFixture f;
  Elaborate(
      "module m(input logic clk, r1, a, b, r2);\n"
      "  property leaf;\n"
      "    @(posedge clk) disable iff (r1) a |-> b;\n"
      "  endproperty\n"
      "  property mid;\n"
      "    @(posedge clk) leaf();\n"
      "  endproperty\n"
      "  property root;\n"
      "    @(posedge clk) disable iff (r2) mid();\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "property \"root\" nests disable iff clauses", 8,
                            "16.12"));
}

TEST(PropertyRewrite,
     FlattenedFormCollectsDisableIffFromSiblingInstancesFromSource) {
  ElabFixture f;
  Elaborate(
      "module m(input logic clk, r1, a, b, r2, c, d);\n"
      "  property l1;\n"
      "    @(posedge clk) disable iff (r1) a |-> b;\n"
      "  endproperty\n"
      "  property l2;\n"
      "    @(posedge clk) disable iff (r2) c |-> d;\n"
      "  endproperty\n"
      "  property root;\n"
      "    @(posedge clk) l1() and l2();\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "property \"root\" nests disable iff clauses", 8,
                            "16.12"));
}

struct Substitution {
  const char* body;
  const char* actual;
  bool clocked = true;
};

enum class Binding : std::uint8_t {
  kPositional,
  kNamed,
  kDefault,
  kThroughAnInstance
};

constexpr const char* kSignals =
    "  bit clk, a, b, c;\n"
    "  int n;\n"
    "  event e1, e2;\n"
    "  parameter int P = 2;\n"
    "  sequence ab; @(posedge clk) a ##1 b; endsequence\n";

std::string Instance(const Substitution& sub, Binding binding,
                     const std::string& callee = "s") {
  std::string decl = "  sequence s(x";
  if (binding == Binding::kDefault) {
    decl += " = ";
    decl += sub.actual;
  }
  decl += "); ";
  decl += sub.body;
  decl += "; endsequence\n";
  std::string call = callee;
  switch (binding) {
    case Binding::kNamed:
      call += "(.x(";
      call += sub.actual;
      call += "))";
      break;
    case Binding::kDefault:
      call += "()";
      break;
    case Binding::kThroughAnInstance:
      decl += "  sequence mid(y); s(y); endsequence\n";
      call = "mid(";
      call += sub.actual;
      call += ")";
      break;
    default:
      call += "(";
      call += sub.actual;
      call += ")";
  }
  std::string out = decl;
  out += "  chk: assert property (";
  if (sub.clocked) out += "@(posedge clk) ";
  out += call;
  out += ");\n";
  return out;
}

std::vector<Diagnostic> DiagnoseModule(const std::string& items) {
  std::string src = "module m;\n";
  src += kSignals;
  src += items;
  src += "endmodule\n";
  ElabFixture f;
  Elaborate(src, f);
  return f.diag.Diagnostics();
}

std::string ErrorsOf(const std::vector<Diagnostic>& diags) {
  std::string out;
  for (const auto& diag : diags) {
    if (diag.severity != DiagSeverity::kError) continue;
    out += std::to_string(diag.loc.line);
    out += ": ";
    out += diag.message;
    out += "\n";
  }
  return out;
}

constexpr uint32_t kCheckLine = 8;

void ExpectIllegal(const std::vector<Substitution>& subs, Binding binding) {
  for (const auto& sub : subs) {
    SCOPED_TRACE(Instance(sub, binding));
    uint32_t line =
        binding == Binding::kThroughAnInstance ? kCheckLine + 1 : kCheckLine;
    EXPECT_TRUE(ReportedError(DiagnoseModule(Instance(sub, binding)), "", line,
                              "16.8"));
  }
}

void ExpectLegal(const std::vector<Substitution>& subs, Binding binding) {
  for (const auto& sub : subs) {
    SCOPED_TRACE(Instance(sub, binding));
    EXPECT_EQ(ErrorsOf(DiagnoseModule(Instance(sub, binding))), "");
  }
}

std::vector<Substitution> SequencesInABooleanPlace() {
  return {{"c ##1 (x == 1)", "a ##1 b"},
          {"c ##1 !x", "a ##1 b"},
          {"c ##1 (x && c)", "a ##1 b"}};
}

std::vector<Substitution> BooleansInABooleanPlace() {
  return {
      {"c ##1 (x == 1)", "a && b"}, {"c ##1 !x", "a"}, {"c ##1 (x && c)", "a"}};
}

std::vector<Substitution> SequencesUnderARepetition() {
  return {{"c ##1 x[->1]", "a ##1 b"}, {"c ##1 x[=2]", "a ##1 b"}};
}

std::vector<Substitution> BooleansUnderARepetition() {
  return {{"c ##1 x[->1]", "a"}, {"c ##1 x[=2]", "a"}};
}

std::vector<Substitution> ExpressionsUnderAMethod() {
  return {{"c ##1 x.triggered", "a ##1 b"}, {"c ##1 x.matched", "a ##1 b"}};
}

std::vector<Substitution> InstancesUnderAMethod() {
  return {{"c ##1 x.triggered", "ab"}, {"c ##1 x.matched", "ab"}};
}

std::vector<Substitution> SequencesAsAClock() {
  return {{"@(x) c", "a ##1 b", false}};
}

std::vector<Substitution> EventsAsAClock() {
  return {{"@(x) c", "posedge clk", false}};
}

std::vector<Substitution> EventsInASequence() {
  return {{"c ##1 x", "posedge clk"},
          {"c ##1 x", "negedge clk"},
          {"c ##1 x", "e1 or e2"},
          {"c ##1 (x == 1)", "posedge clk"}};
}

std::vector<Substitution> PropertiesInASequence() {
  return {
      {"c ##1 x", "not a"}, {"c ##1 x", "a |-> b"}, {"c ##1 x", "a until b"}};
}

std::vector<Substitution> SequencesInASequence() {
  return {{"c ##1 x", "a ##1 b"}};
}

std::vector<Substitution> VariablesAsABound() {
  return {{"c ##[1:x] a", "n"},
          {"c ##1 a[->x]", "n"},
          {"c ##1 a[=x]", "n"},
          {"c ##1 a[*x]", "n"}};
}

std::vector<Substitution> ConstantsAsABound() {
  return {{"c ##[1:x] a", "P"}, {"c ##1 a[->x]", "P"}, {"c ##1 a[=x]", "P"},
          {"c ##1 a[*x]", "P"}, {"c ##[1:x] a", "2"},  {"c ##1 a[->x]", "2"},
          {"c ##1 a[=x]", "2"}, {"c ##1 a[*x]", "2"}};
}

constexpr Binding kBindings[] = {Binding::kPositional, Binding::kNamed,
                                 Binding::kDefault,
                                 Binding::kThroughAnInstance};

TEST(FlattenedSequence, DISABLED_ASequenceInABooleanPlaceIsIllegal) {
  for (Binding binding : kBindings)
    ExpectIllegal(SequencesInABooleanPlace(), binding);
}

TEST(FlattenedSequence, ABooleanInABooleanPlaceIsLegal) {
  for (Binding binding : kBindings)
    ExpectLegal(BooleansInABooleanPlace(), binding);
}

TEST(FlattenedSequence,
     DISABLED_ASequenceUnderAGotoOrNonconsecutiveRepetitionIsIllegal) {
  for (Binding binding : kBindings)
    ExpectIllegal(SequencesUnderARepetition(), binding);
}

TEST(FlattenedSequence, ABooleanUnderAGotoOrNonconsecutiveRepetitionIsLegal) {
  for (Binding binding : kBindings)
    ExpectLegal(BooleansUnderARepetition(), binding);
}

TEST(FlattenedSequence, DISABLED_AnExpressionUnderASequenceMethodIsIllegal) {
  for (Binding binding : kBindings)
    ExpectIllegal(ExpressionsUnderAMethod(), binding);
}

TEST(FlattenedSequence, AnInstanceUnderASequenceMethodIsLegal) {
  for (Binding binding : kBindings)
    ExpectLegal(InstancesUnderAMethod(), binding);
}

TEST(FlattenedSequence, DISABLED_ASequenceAsAClockingEventIsIllegal) {
  for (Binding binding : kBindings) ExpectIllegal(SequencesAsAClock(), binding);
}

TEST(FlattenedSequence, AnEventAsAClockingEventIsLegal) {
  for (Binding binding : kBindings) ExpectLegal(EventsAsAClock(), binding);
}

TEST(FlattenedSequence, DISABLED_AnEventExpressionInASequenceIsIllegal) {
  for (Binding binding : kBindings) ExpectIllegal(EventsInASequence(), binding);
}

TEST(FlattenedSequence, DISABLED_APropertyInASequenceIsIllegal) {
  for (Binding binding : kBindings)
    ExpectIllegal(PropertiesInASequence(), binding);
}

TEST(FlattenedSequence, ASequenceWhereASequenceStandsIsLegal) {
  for (Binding binding : kBindings)
    ExpectLegal(SequencesInASequence(), binding);
}

TEST(FlattenedSequence, AVariableAsADelayOrRepetitionBoundIsIllegal) {
  ExpectIllegal(VariablesAsABound(), Binding::kPositional);
}

TEST(FlattenedSequence,
     DISABLED_AVariableBoundByNameDefaultOrInstanceIsIllegal) {
  for (Binding binding :
       {Binding::kNamed, Binding::kDefault, Binding::kThroughAnInstance})
    ExpectIllegal(VariablesAsABound(), binding);
}

TEST(FlattenedSequence, AConstantAsADelayOrRepetitionBoundIsLegal) {
  for (Binding binding : kBindings) ExpectLegal(ConstantsAsABound(), binding);
}

struct Place {
  const char* name;
  const char* before;
  const char* after;
  const char* callee;
};

std::vector<Place> Places() {
  return {
      {"module", "module m;\n", "endmodule\n", "s"},
      {"interface", "interface ifc;\n",
       "endinterface\nmodule m;\n  ifc u();\nendmodule\n", "s"},
      {"program", "program prg;\n",
       "endprogram\nmodule m;\n  prg u();\nendmodule\n", "s"},
      {"checker", "checker ck;\n",
       "endchecker\nmodule m;\n  ck u();\nendmodule\n", "s"},
      {"generate block", "module m;\n  if (1) begin : g\n",
       "  end\nendmodule\n", "s"},
  };
}

std::string InPlace(const Place& place, const char* actual) {
  std::string src = place.before;
  src += "  bit clk, a, b, c;\n";
  src +=
      Instance({"c ##1 (x == 1)", actual}, Binding::kPositional, place.callee);
  src += place.after;
  return src;
}

std::string InPackage(const char* actual) {
  std::string src = "package pk;\n  bit clk, a, b, c;\n";
  src += "  sequence s(x); c ##1 (x == 1); endsequence\nendpackage\n";
  src += "module m;\n  import pk::clk, pk::a, pk::b;\n";
  src += "  chk: assert property (@(posedge clk) pk::s(";
  src += actual;
  src += "));\nendmodule\n";
  return src;
}

std::vector<Diagnostic> DiagnoseSource(const std::string& src) {
  ElabFixture f;
  Elaborate(src, f);
  return f.diag.Diagnostics();
}

TEST(FlattenedSequence, DISABLED_AnIllegalSubstitutionIsReportedInEachPlace) {
  for (const auto& place : Places()) {
    std::string src = InPlace(place, "a ##1 b");
    SCOPED_TRACE(place.name);
    EXPECT_TRUE(ReportedError(DiagnoseSource(src), "", LineHolding(src, "chk:"),
                              "16.8"));
  }
  std::string src = InPackage("a ##1 b");
  EXPECT_TRUE(
      ReportedError(DiagnoseSource(src), "", LineHolding(src, "chk:"), "16.8"));
}

TEST(FlattenedSequence, ALegalSubstitutionIsAcceptedInEachPlace) {
  for (const auto& place : Places()) {
    SCOPED_TRACE(place.name);
    EXPECT_EQ(ErrorsOf(DiagnoseSource(InPlace(place, "a && b"))), "");
  }
  EXPECT_EQ(ErrorsOf(DiagnoseSource(InPackage("a && b"))), "");
}

struct Use {
  const char* before;
  const char* after;
};

std::vector<Use> Uses() {
  return {{"  chk: assert property (", ");\n"},
          {"  chk: assume property (", ");\n"},
          {"  chk: cover property (", ");\n"},
          {"  property chk; ", "; endproperty\n"},
          {"  sequence chk; ", "; endsequence\n"},
          {"  always @(", ") begin end\n"}};
}

std::string InUse(const Use& use, const char* actual) {
  std::string src = "module m;\n";
  src += kSignals;
  src += "  sequence s(x); @(posedge clk) c ##1 (x == 1); endsequence\n";
  src += use.before;
  src += "s(";
  src += actual;
  src += ")";
  src += use.after;
  src += "endmodule\n";
  return src;
}

TEST(FlattenedSequence, DISABLED_AnIllegalSubstitutionIsReportedInEachUse) {
  for (const auto& use : Uses()) {
    std::string src = InUse(use, "a ##1 b");
    SCOPED_TRACE(src);
    EXPECT_TRUE(ReportedError(DiagnoseSource(src), "", kCheckLine, "16.8"));
  }
}

TEST(FlattenedSequence, ALegalSubstitutionIsAcceptedInEachUse) {
  for (const auto& use : Uses()) {
    std::string src = InUse(use, "a && b");
    SCOPED_TRACE(src);
    EXPECT_EQ(ErrorsOf(DiagnoseSource(src)), "");
  }
}

std::string DefaultedBy(const std::string& kind, const std::string& formals,
                        const std::string& body) {
  return "module m;\n"
         "  logic clk, b, v;\n"
         "  " +
         kind + " s(" + formals + ");\n    " + body + ";\n  end" + kind +
         "\n"
         "  cover property (@(posedge clk) s(b));\n"
         "endmodule\n";
}

void ExpectDefaultUnresolved(const std::string& formals,
                             const std::string& body, const std::string& name) {
  for (const char* kind : {"sequence", "property"}) {
    std::string src = DefaultedBy(kind, formals, body);
    SCOPED_TRACE(src);
    EXPECT_TRUE(ReportedError(
        DiagnoseSource(src),
        "reference to unresolved identifier '" + name + "'", 3, "23.9"));
  }
}

TEST(DefaultActualNames, DISABLED_AnUndeclaredNameIsUnresolved) {
  ExpectDefaultUnresolved("c, x = zz", "c ##1 x", "zz");
}

TEST(DefaultActualNames, DISABLED_AnotherFormalIsUnresolved) {
  ExpectDefaultUnresolved("x, y = x", "x ##1 y", "x");
}

TEST(DefaultActualNames, DISABLED_AnotherFormalOfALocalFormalIsUnresolved) {
  ExpectDefaultUnresolved("c, local input logic d = c", "c ##1 d", "c");
}

TEST(DefaultActualNames, AModuleVariableIsAccepted) {
  for (const char* kind : {"sequence", "property"}) {
    std::string src =
        DefaultedBy(kind, "x, y = b, local input logic d = v", "x ##1 y ##1 d");
    SCOPED_TRACE(src);
    EXPECT_EQ(ErrorsOf(DiagnoseSource(src)), "");
  }
}

}  // namespace
