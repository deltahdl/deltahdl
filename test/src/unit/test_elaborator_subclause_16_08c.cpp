#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr char kExcess[] =
    "sequence instance provides more actual arguments than the sequence has "
    "formal arguments";

constexpr char kUnknown[] =
    "sequence instance names 'z', which is not a formal argument of the "
    "sequence";

constexpr char kTwice[] =
    "sequence instance binds the formal 'x' more than once";

const char kBindDecl[] = "sequence s(x, y = 1); x ##1 y; endsequence\n";

const char kBindTaker[] =
    "sequence s(x, y = 1); @(posedge clk) x ##1 y; endsequence\n";

std::string Source(const std::string& takers, const std::string& use) {
  return "module m;\n"
         "  bit clk, a, b;\n"
         "  " +
         takers + "  " + use + "\nendmodule\n";
}

std::string BindSource(const std::string& use) {
  return Source(kBindTaker, use);
}

void ExpectReported(const std::string& src, const std::string& use,
                    const char* message) {
  SCOPED_TRACE(use);
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message,
                            LineHolding(src, use), "16.8"));
}

void ExpectAccepted(const std::string& src, const std::string& use) {
  SCOPED_TRACE(use);
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_FALSE(ErrorOnLine(f.diag.Diagnostics(), LineHolding(src, use)));
}

std::string Call(const std::string& actuals) { return "s(" + actuals + ")"; }

std::vector<std::string> InstanceSites(const std::string& inst) {
  return {"initial @(" + inst + ") $display(\"x\");",
          "assert property (" + inst + ");",
          "assume property (" + inst + ");",
          "cover property (" + inst + ");",
          "cover sequence (" + inst + ");",
          "always @(posedge clk) assert property (" + inst + ");",
          "sequence t; " + inst + "; endsequence",
          "property p; " + inst + "; endproperty",
          "initial wait (" + inst + ".triggered);",
          "sequence u; @(posedge clk) a ##1 " + inst + ".matched; endsequence",
          "if (1) begin : g assert property (" + inst + "); end"};
}

TEST(SequenceActualBinding, AnExcessPositionalActualInAnEventControl) {
  const std::string kUse = "initial @(s(a, b, a)) $display(\"x\");";
  ExpectReported(BindSource(kUse), kUse, kExcess);
}

TEST(SequenceActualBinding, DISABLED_AnExcessPositionalActualElsewhere) {
  auto sites = InstanceSites(Call("a, b, a"));
  sites.erase(sites.begin());
  for (const auto& use : sites) {
    ExpectReported(BindSource(use), use, kExcess);
  }
}

TEST(SequenceActualBinding, DISABLED_AnEmptyTrailingSlotPastTheLastFormal) {
  for (const auto& use : InstanceSites(Call("a, b, "))) {
    ExpectReported(BindSource(use), use, kExcess);
  }
}

TEST(SequenceActualBinding, DISABLED_ANamedActualNamingNoFormalIsReported) {
  for (const auto& use : InstanceSites(Call(".x(a), .z(b)"))) {
    ExpectReported(BindSource(use), use, kUnknown);
  }
}

TEST(SequenceActualBinding, DISABLED_AFormalNamedTwiceIsReported) {
  for (const auto& use : InstanceSites(Call(".x(a), .x(b)"))) {
    ExpectReported(BindSource(use), use, kTwice);
  }
}

TEST(SequenceActualBinding, DISABLED_AFormalBoundByPositionThenByName) {
  for (const auto& use : InstanceSites(Call("a, .x(b)"))) {
    ExpectReported(BindSource(use), use, kTwice);
  }
}

TEST(SequenceActualBinding, EveryFormalBoundOnceIsAccepted) {
  for (const char* actuals :
       {"a, b", "a", "a, ", ".x(a), .y(b)", ".y(b), .x(a)", ".x(a)", "a, .y(b)",
        ".x(a), .y()"}) {
    for (const auto& use : InstanceSites(Call(actuals))) {
      ExpectAccepted(BindSource(use), use);
    }
  }
}

struct ScopePlace {
  std::string place;
  std::string src;
  std::string use;
};

std::string Assertion(const std::string& prefix, const std::string& call) {
  return "assert property (@(posedge clk) " + prefix + call + ");";
}

std::vector<ScopePlace> ScopePlaces(const std::string& decl,
                                    const std::string& call) {
  const std::string kHere = Assertion("", call);
  const std::string kModule = "module m;\n  bit clk, a, b;\n  ";
  return {
      {"package scope",
       "package pk;\n  " + decl + "endpackage\n" + kModule +
           Assertion("pk::", call) + "\nendmodule\n",
       Assertion("pk::", call)},
      {"package import",
       "package pk;\n  " + decl + "endpackage\n" + kModule +
           "import pk::*;\n  " + kHere + "\nendmodule\n",
       kHere},
      {"interface instance",
       "interface ifc;\n  " + decl + "endinterface\n" + kModule +
           "ifc i();\n  " + Assertion("i.", call) + "\nendmodule\n",
       Assertion("i.", call)},
      {"interface",
       "interface ifc;\n  bit clk, a, b;\n  " + decl + "  " + kHere +
           "\nendinterface\nmodule m;\n  ifc i();\nendmodule\n",
       kHere},
      {"program",
       "program pg;\n  bit clk, a, b;\n  " + decl + "  " + kHere +
           "\nendprogram\n",
       kHere},
      {"clocking block",
       kModule + "clocking cb @(posedge clk);\n    " + decl +
           "  endclocking\n  " + Assertion("cb.", call) + "\nendmodule\n",
       Assertion("cb.", call)},
      {"checker",
       "checker ck(bit clk, bit a, bit b);\n  " + decl + "  " + kHere +
           "\nendchecker\n" + kModule + "ck k(clk, a, b);\nendmodule\n",
       kHere},
      {"generate block",
       kModule + "if (1) begin : g\n    " + decl + "    " + kHere +
           "\n  end\nendmodule\n",
       kHere},
      {"compilation unit", decl + kModule + kHere + "\nendmodule\n", kHere}};
}

TEST(SequenceActualBinding, DISABLED_AnExcessPositionalActualInEveryScope) {
  for (const auto& placed : ScopePlaces(kBindDecl, Call("a, b, a"))) {
    SCOPED_TRACE(placed.place);
    ExpectReported(placed.src, placed.use, kExcess);
  }
}

TEST(SequenceActualBinding, DISABLED_ANamedActualNamingNoFormalInEveryScope) {
  for (const auto& placed : ScopePlaces(kBindDecl, Call(".z(b)"))) {
    SCOPED_TRACE(placed.place);
    ExpectReported(placed.src, placed.use, kUnknown);
  }
}

TEST(SequenceActualBinding, EveryFormalBoundOnceInEveryScopeIsAccepted) {
  for (const char* actuals : {"a, b", ".x(a), .y(b)", "a, .y(b)"}) {
    for (const auto& placed : ScopePlaces(kBindDecl, Call(actuals))) {
      SCOPED_TRACE(placed.place);
      ExpectAccepted(placed.src, placed.use);
    }
  }
}

constexpr char kDollar[] =
    "shall be untyped and referenced only as the upper bound of a cycle delay "
    "range or as an actual argument of an instance";

struct InstanceForm {
  const char* decls;
  const char* call;
};

std::string FormUse(const std::string& call) {
  return "a1: assert property (@(posedge clk) " + call + ");";
}

const char kFormNames[] =
    "int z;\n"
    "  bit c;\n"
    "  parameter int P = 2;\n"
    "  localparam int L = 3;\n"
    "  ";

std::string FormSource(const InstanceForm& form) {
  return Source(kFormNames + std::string(form.decls) + "\n",
                FormUse(form.call));
}

size_t CountReports(const std::vector<Diagnostic>& diags, const char* message) {
  size_t count = 0;
  for (const auto& diag : diags) {
    if (diag.message.find(message) != std::string::npos) ++count;
  }
  return count;
}

const InstanceForm kDollarForbidden[] = {
    {"sequence s(k); a ##[k:5] b; endsequence", "s($)"},
    {"sequence s(k); a ##k b; endsequence", "s($)"},
    {"sequence s(k); a ##1 b[*k]; endsequence", "s($)"},
    {"sequence s(k); a ##1 b[=k]; endsequence", "s($)"},
    {"sequence s(k); a ##1 b[->k]; endsequence", "s($)"},
    {"sequence s(k); a ##[1:k] b ##1 (a == k); endsequence", "s($)"},
    {"sequence r(j); a ##[1:j] b; endsequence\n"
     "  sequence s(k); a ##1 r(k + 1); endsequence",
     "s($)"},
    {"sequence s(sequence k); a ##1 k; endsequence", "s($)"},
    {"sequence s(local input int k); a ##[1:k] b; endsequence", "s($)"},
    {"sequence s(k); a ##k b; endsequence", "s(.k($))"}};

const InstanceForm kDollarAllowed[] = {
    {"sequence s(k); a ##[5:k] b; endsequence", "s($)"},
    {"sequence s(k); a ##1 b[*1:k]; endsequence", "s($)"},
    {"sequence s(k); a ##1 b[=1:k]; endsequence", "s($)"},
    {"sequence s(k); a ##1 b[->1:k]; endsequence", "s($)"},
    {"sequence s(k); (a ##1 b)[*1:k]; endsequence", "s($)"},
    {"sequence s(untyped k); a ##[1:k] b; endsequence", "s($)"},
    {"sequence r(j); a ##[1:j] b; endsequence\n"
     "  sequence s(k); a ##1 r(k); endsequence",
     "s($)"},
    {"sequence s(k); a ##[1:k] b; endsequence", "s(.k($))"}};

const InstanceForm kDollarOverridden[] = {
    {"sequence s(k = $); a ##k b; endsequence", "s(3)"},
    {"sequence s(int k = $); a ##k b; endsequence", "s(.k(2))"}};

TEST(SequenceDollarActual, EveryForbiddenReferenceIsReported) {
  for (const auto& form : kDollarForbidden) {
    SCOPED_TRACE(form.decls);
    ExpectReported(FormSource(form), FormUse(form.call), kDollar);
  }
}

TEST(SequenceDollarActual, EveryAllowedReferenceIsAccepted) {
  for (const auto& form : kDollarAllowed) {
    SCOPED_TRACE(form.decls);
    ExpectAccepted(FormSource(form), FormUse(form.call));
  }
}

TEST(SequenceDollarActual, DISABLED_AnOverriddenDefaultDollarIsAccepted) {
  for (const auto& form : kDollarOverridden) {
    SCOPED_TRACE(form.decls);
    ExpectAccepted(FormSource(form), FormUse(form.call));
  }
}

TEST(SequenceDollarActual, DISABLED_ADefaultDollarLeftInPlaceIsReportedOnce) {
  for (const char* decls : {"sequence s(int k = $); a ##[1:k] b; endsequence",
                            "sequence s(k = $); a ##1 (b == k); endsequence"}) {
    SCOPED_TRACE(decls);
    const InstanceForm kForm = {decls, "s()"};
    const std::string kSrc = FormSource(kForm);
    ElabFixture f;
    ElaborateSrc(kSrc, f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kDollar,
                              LineHolding(kSrc, FormUse("s()")), "16.8"));
    EXPECT_EQ(CountReports(f.diag.Diagnostics(), kDollar), 1u);
  }
}

TEST(SequenceDollarActual, ADefaultDollarNeverInstantiatedIsAccepted) {
  ElabFixture f;
  ElaborateSrc(Source("sequence s(int k = $); a ##[1:k] b; endsequence\n", ""),
               f);
  EXPECT_EQ(CountReports(f.diag.Diagnostics(), kDollar), 0u);
}

const char kDollarTakers[] =
    "sequence bad(k); @(posedge clk) a ##k b; endsequence\n"
    "  sequence good(k); @(posedge clk) a ##[1:k] b; endsequence\n";

bool AnEventOrTriggeredOrGenerateSite(const std::string& use) {
  return use.starts_with("initial @(") ||
         use.find(".triggered") != std::string::npos ||
         use.find("begin : g") != std::string::npos;
}

TEST(SequenceDollarActual, AForbiddenInstanceIsReportedAtMostSites) {
  for (const auto& use : InstanceSites("bad($)")) {
    if (AnEventOrTriggeredOrGenerateSite(use)) continue;
    ExpectReported(Source(kDollarTakers, use), use, kDollar);
  }
}

TEST(SequenceDollarActual, DISABLED_AForbiddenInstanceIsReportedAtEverySite) {
  for (const auto& use : InstanceSites("bad($)")) {
    if (!AnEventOrTriggeredOrGenerateSite(use)) continue;
    ExpectReported(Source(kDollarTakers, use), use, kDollar);
  }
}

TEST(SequenceDollarActual, AnAllowedInstanceIsAcceptedAtEverySite) {
  for (const auto& use : InstanceSites("good($)")) {
    ExpectAccepted(Source(kDollarTakers, use), use);
  }
}

const char kDollarDecl[] =
    "sequence bad(x, k); x ##k x; endsequence\n"
    "  sequence good(x, k); x ##[1:k] x; endsequence\n";

bool DeclaredWhereItIsInstantiated(const std::string& place) {
  return place == "interface" || place == "program" || place == "checker";
}

bool NamedThroughAScope(const std::string& place) {
  return place == "package scope" || place == "interface instance" ||
         place == "clocking block";
}

TEST(SequenceDollarActual, AForbiddenInstanceIsReportedInADesignElement) {
  for (const auto& placed : ScopePlaces(kDollarDecl, "bad(a, $)")) {
    if (!DeclaredWhereItIsInstantiated(placed.place)) continue;
    SCOPED_TRACE(placed.place);
    ExpectReported(placed.src, placed.use, kDollar);
  }
}

TEST(SequenceDollarActual, DISABLED_AForbiddenInstanceIsReportedInEveryScope) {
  for (const auto& placed : ScopePlaces(kDollarDecl, "bad(a, $)")) {
    if (DeclaredWhereItIsInstantiated(placed.place)) continue;
    SCOPED_TRACE(placed.place);
    ExpectReported(placed.src, placed.use, kDollar);
  }
}

TEST(SequenceDollarActual, AnAllowedInstanceNamedSimplyIsAccepted) {
  for (const auto& placed : ScopePlaces(kDollarDecl, "good(a, $)")) {
    if (NamedThroughAScope(placed.place)) continue;
    SCOPED_TRACE(placed.place);
    ExpectAccepted(placed.src, placed.use);
  }
}

TEST(SequenceDollarActual, DISABLED_AnAllowedInstanceNamedThroughAScope) {
  for (const auto& placed : ScopePlaces(kDollarDecl, "good(a, $)")) {
    if (!NamedThroughAScope(placed.place)) continue;
    SCOPED_TRACE(placed.place);
    ExpectAccepted(placed.src, placed.use);
  }
}

constexpr char kNonConstant[] = "is not an elaboration-time constant";

const char* const kBoundForms[] = {
    "sequence s(n); a ##[n:5] b; endsequence",
    "sequence s(n); a ##[1:n] b; endsequence",
    "sequence s(n); a ##1 b[*n]; endsequence",
    "sequence s(n); a ##1 b[*1:n]; endsequence",
    "sequence s(n); a ##1 b[=n]; endsequence",
    "sequence s(n); a ##1 b[=n:5]; endsequence",
    "sequence s(n); a ##1 b[=1:n]; endsequence",
    "sequence s(n); a ##1 b[->n]; endsequence",
    "sequence s(n); a ##1 b[->n:5]; endsequence",
    "sequence s(n); a ##1 b[->1:n]; endsequence",
    "sequence s(n); (a ##1 b)[*n]; endsequence",
    "sequence s(n); (a ##1 b)[*1:n]; endsequence"};

const char* const kUpperBoundForms[] = {
    "sequence s(n); a ##[1:n] b; endsequence",
    "sequence s(n); a ##1 b[*1:n]; endsequence",
    "sequence s(n); a ##1 b[=1:n]; endsequence",
    "sequence s(n); a ##1 b[->1:n]; endsequence",
    "sequence s(n); (a ##1 b)[*1:n]; endsequence"};

TEST(SequenceConstantBound, AVariableActualInEveryBoundIsReported) {
  for (const char* decls : kBoundForms) {
    SCOPED_TRACE(decls);
    const InstanceForm kForm = {decls, "s(z)"};
    ExpectReported(FormSource(kForm), FormUse(kForm.call), kNonConstant);
  }
}

TEST(SequenceConstantBound, AConstantActualInEveryBoundIsAccepted) {
  for (const char* decls : kBoundForms) {
    for (const char* call : {"s(2)", "s(P)", "s(L + 1)"}) {
      SCOPED_TRACE(std::string(decls) + " " + call);
      const InstanceForm kForm = {decls, call};
      ExpectAccepted(FormSource(kForm), FormUse(kForm.call));
    }
  }
  for (const char* decls : kUpperBoundForms) {
    SCOPED_TRACE(decls);
    const InstanceForm kForm = {decls, "s($)"};
    ExpectAccepted(FormSource(kForm), FormUse(kForm.call));
  }
}

const InstanceForm kNonConstantActuals[] = {
    {"sequence s(n); a ##[1:n] b; endsequence", "s(z + 1)"},
    {"sequence s(n); a ##[1:n] b; endsequence", "s(-z)"},
    {"sequence s(n); a ##1 b[*n]; endsequence", "s(z[1:0])"},
    {"sequence s(n); a ##1 b[*n]; endsequence", "s(c ? 1 : 2)"},
    {"sequence s(n = z); a ##[1:n] b; endsequence", "s()"},
    {"sequence r(n); a ##[1:n] b; endsequence\n"
     "  sequence s(k); a ##1 r(k); endsequence",
     "s(z)"},
    {"sequence r(n); a ##[1:n] b; endsequence\n"
     "  property q(k); a |-> r(k); endproperty",
     "q(z)"},
    {"sequence r(n); a ##[1:n] b; endsequence\n"
     "  sequence s(k = z); a ##1 r(k); endsequence",
     "s()"}};

const InstanceForm kConstantActuals[] = {
    {"sequence s(n); a ##[1:n] b; endsequence", "s(P + 1)"},
    {"sequence s(n); a ##[1:n] b; endsequence", "s(L * 2)"},
    {"sequence s(n = P); a ##[1:n] b; endsequence", "s()"},
    {"sequence s(n = 2); a ##[1:n] b; endsequence", "s()"},
    {"sequence s(n = z); a ##[1:n] b; endsequence", "s(2)"},
    {"sequence r(n); a ##[1:n] b; endsequence\n"
     "  sequence s(k); a ##1 r(k); endsequence",
     "s(P)"},
    {"sequence r(n); a ##[1:n] b; endsequence\n"
     "  property q(k); a |-> r(k); endproperty",
     "q(2)"},
    {"sequence r(n); a ##[1:n] b; endsequence\n"
     "  sequence s(k = P); a ##1 r(k); endsequence",
     "s()"}};

TEST(SequenceConstantBound, DISABLED_EveryNonConstantActualIsReported) {
  for (const auto& form : kNonConstantActuals) {
    SCOPED_TRACE(std::string(form.decls) + " " + form.call);
    ExpectReported(FormSource(form), FormUse(form.call), kNonConstant);
  }
}

TEST(SequenceConstantBound, EveryConstantActualIsAccepted) {
  for (const auto& form : kConstantActuals) {
    SCOPED_TRACE(std::string(form.decls) + " " + form.call);
    ExpectAccepted(FormSource(form), FormUse(form.call));
  }
}

std::string BoundTakers() {
  return std::string(kFormNames) +
         "sequence s7(n); @(posedge clk) a ##[1:n] b; endsequence\n";
}

bool AProceduralOrGenerateSite(const std::string& use) {
  return use.starts_with("initial") || use.starts_with("always") ||
         use.find("begin : g") != std::string::npos;
}

TEST(SequenceConstantBound, AVariableActualIsReportedAtMostSites) {
  for (const auto& use : InstanceSites("s7(z)")) {
    if (AProceduralOrGenerateSite(use)) continue;
    ExpectReported(Source(BoundTakers(), use), use, kNonConstant);
  }
}

TEST(SequenceConstantBound, DISABLED_AVariableActualIsReportedAtEverySite) {
  for (const auto& use : InstanceSites("s7(z)")) {
    if (!AProceduralOrGenerateSite(use)) continue;
    ExpectReported(Source(BoundTakers(), use), use, kNonConstant);
  }
}

TEST(SequenceConstantBound, AParameterActualIsAcceptedAtEverySite) {
  for (const auto& use : InstanceSites("s7(P)")) {
    ExpectAccepted(Source(BoundTakers(), use), use);
  }
}

const char kBoundDecl[] = "sequence s7(x, n); x ##[1:n] x; endsequence\n";

bool AnInterfaceOrProgram(const std::string& place) {
  return place == "interface" || place == "program";
}

TEST(SequenceConstantBound, AVariableActualIsReportedInAnInterfaceOrProgram) {
  for (const auto& placed : ScopePlaces(kBoundDecl, "s7(a, a)")) {
    if (!AnInterfaceOrProgram(placed.place)) continue;
    SCOPED_TRACE(placed.place);
    ExpectReported(placed.src, placed.use, kNonConstant);
  }
}

TEST(SequenceConstantBound, DISABLED_AVariableActualIsReportedInEveryScope) {
  for (const auto& placed : ScopePlaces(kBoundDecl, "s7(a, a)")) {
    if (AnInterfaceOrProgram(placed.place)) continue;
    SCOPED_TRACE(placed.place);
    ExpectReported(placed.src, placed.use, kNonConstant);
  }
}

TEST(SequenceConstantBound, ALiteralActualIsAcceptedInEveryScope) {
  for (const auto& placed : ScopePlaces(kBoundDecl, "s7(a, 2)")) {
    SCOPED_TRACE(placed.place);
    ExpectAccepted(placed.src, placed.use);
  }
}

}  // namespace
