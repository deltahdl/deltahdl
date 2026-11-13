#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr const char* kPassingReport =
    "an actual shall be passed by value as an input or by reference";

bool PassingReportedAt(const std::vector<Diagnostic>& diags, uint32_t line,
                       uint32_t column) {
  for (const Diagnostic& d : diags) {
    if (d.severity == DiagSeverity::kError && d.loc.line == line &&
        d.loc.column == column &&
        d.message.find(kPassingReport) != std::string::npos) {
      return true;
    }
  }
  return false;
}

void ExpectPassingReported(const std::string& src, const std::string& call) {
  SCOPED_TRACE(src);
  ElabFixture f;
  ElaborateSrc(src, f);
  uint32_t line = LineHolding(src, call);
  ASSERT_NE(line, 0u);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kPassingReport, line, "16.11"));
}

struct CalleeKind {
  const char* outside;
  const char* items;
  const char* call;
};

const CalleeKind kCalleeKinds[] = {
    {"", "task automatic t(@D int v); endtask", "t(count)"},
    {"", "function automatic void f(@D int v); endfunction", "f(count)"},
    {"", "class C; task t(@D int v); endtask endclass\n  C h = new;",
     "h.t(count)"},
    {"",
     "class C; function void f(@D int v); endfunction endclass\n"
     "  C h = new;",
     "h.f(count)"},
    {"", "class C; static task t(@D int v); endtask endclass", "C::t(count)"},
    {"package Q; task automatic t(@D int v); endtask endpackage\n", "",
     "Q::t(count)"},
    {"package Q; task automatic t(@D int v); endtask endpackage\n",
     "import Q::t;", "t(count)"},
    {"package Q; task automatic t(@D int v); endtask endpackage\n",
     "import Q::*;", "t(count)"},
    {"task automatic ut(@D int v); endtask\n", "", "ut(count)"},
    {"", "function automatic int nf(@D int v); return 0; endfunction",
     "nf(count)"},
};

std::string WithDirection(std::string text, const std::string& direction) {
  for (size_t at = text.find("@D"); at != std::string::npos;
       at = text.find("@D")) {
    text.replace(at, 2, direction);
  }
  return text;
}

std::string CalleeModule(const CalleeKind& kind, const std::string& direction) {
  return WithDirection(kind.outside, direction) +
         "module m;\n"
         "  bit clk, a;\n"
         "  int count;\n"
         "  " +
         WithDirection(kind.items, direction) +
         "\n"
         "  sequence s; @(posedge clk) (a, " +
         kind.call +
         ") ##1 a; endsequence\n"
         "endmodule\n";
}

TEST(AttachedArgumentPassing, AnOutputOrInoutFormalOfEachCalleeKindIsReported) {
  for (const CalleeKind& kind : kCalleeKinds) {
    for (const char* direction : {"output", "inout"}) {
      ExpectPassingReported(CalleeModule(kind, direction), kind.call);
    }
  }
}

TEST(AttachedArgumentPassing,
     AnInputOrReferenceFormalOfEachCalleeKindIsAccepted) {
  for (const CalleeKind& kind : kCalleeKinds) {
    for (const char* direction : {"input", "ref", "const ref"}) {
      std::string src = CalleeModule(kind, direction);
      SCOPED_TRACE(src);
      ElabFixture f;
      ElaborateSrc(src, f);
      EXPECT_FALSE(f.diag.HasErrors());
    }
  }
}

std::string BindingModule(const std::string& call) {
  return "module m;\n"
         "  bit clk, a;\n"
         "  int count;\n"
         "  task automatic t3(input int x, input int z = 0, output int y);"
         " y = x; endtask\n"
         "  task automatic t2(input int x, output int y); y = x; endtask\n"
         "  task automatic tr(input int x, ref int r); endtask\n"
         "  sequence s; @(posedge clk) (a, " +
         call +
         ") ##1 a; endsequence\n"
         "endmodule\n";
}

void ExpectReportedAtCount(const std::string& call) {
  std::string src = BindingModule(call);
  SCOPED_TRACE(src);
  ElabFixture f;
  ElaborateSrc(src, f);
  uint32_t line = LineHolding(src, call);
  ASSERT_NE(line, 0u);
  size_t start = src.find(call);
  size_t line_start = src.rfind('\n', start) + 1;
  size_t count_at = src.find("count", start);
  size_t one_at = src.find('1', start);
  EXPECT_TRUE(
      PassingReportedAt(f.diag.Diagnostics(), line,
                        static_cast<uint32_t>(count_at - line_start + 1)));
  EXPECT_FALSE(
      PassingReportedAt(f.diag.Diagnostics(), line,
                        static_cast<uint32_t>(one_at - line_start + 1)));
}

TEST(AttachedArgumentPassing, APositionalOutputActualIsReportedAtTheActual) {
  ExpectReportedAtCount("t3(1, , count)");
  ExpectReportedAtCount("t2(1, count)");
}

TEST(AttachedArgumentPassing,
     DISABLED_ANamedOutputActualIsReportedAtTheActual) {
  ExpectReportedAtCount("t3(.y(count), .x(1))");
  ExpectReportedAtCount("t2(.y(count), .x(1))");
  ExpectReportedAtCount("t2(.x(1), .y(count))");
}

TEST(AttachedArgumentPassing, NamedInputAndReferenceActualsAreAccepted) {
  for (const char* call :
       {"tr(.x(count), .r(count))", "tr(.r(count), .x(1))"}) {
    std::string src = BindingModule(call);
    SCOPED_TRACE(src);
    ElabFixture f;
    ElaborateSrc(src, f);
    EXPECT_FALSE(f.diag.HasErrors());
  }
}

std::vector<const char*> CheckedPlaces() {
  return {"interface", "program", "checker", "property", "assertion", "always"};
}

std::vector<const char*> OuterPlaces() {
  return {"package sequence",   "package property",  "unit sequence",
          "unit property",      "generate sequence", "generate property",
          "generate assertion", "generate always",   "clocking sequence",
          "clocking property"};
}

struct PlaceParts {
  std::string tasks =
      "task automatic tout(output int v); v = 1; endtask\n"
      "task automatic tio(inout int v); v++; endtask\n"
      "task automatic tin(input int v); endtask\n";
  std::string vars = "  bit clk, a;\n  int count;\n";
  std::string checker_vars = "  int count;\n";
  std::string group;
  std::string seq;
  std::string prop;
};

PlaceParts PartsFor(const std::string& call) {
  PlaceParts parts;
  parts.group = "(a, " + call + ") ##1 a";
  parts.seq = "  sequence s; @(posedge clk) " + parts.group + "; endsequence\n";
  parts.prop =
      "  property p; @(posedge clk) " + parts.group + "; endproperty\n";
  return parts;
}

std::string ElementPlace(const std::string& place, const PlaceParts& x) {
  if (place == "interface" || place == "program") {
    return x.tasks + place + " el;\n" + x.vars + x.seq + "end" + place +
           "\nmodule m; el u(); endmodule\n";
  }
  if (place == "checker") {
    return x.tasks + "checker el(bit clk, bit a);\n" + x.checker_vars + x.seq +
           "endchecker\nmodule m;\n  bit clk, a;\n  el u(clk, a);\n"
           "endmodule\n";
  }
  std::string item = x.prop;
  if (place == "assertion") {
    item = "  assert property (@(posedge clk) " + x.group + ");\n";
  } else if (place == "always") {
    item = "  always @(posedge clk) assert property (" + x.group + ");\n";
  }
  return x.tasks + "module m;\n" + x.vars + item + "endmodule\n";
}

std::string GenerateItem(const std::string& place, const PlaceParts& x) {
  if (place == "generate sequence") return x.seq;
  if (place == "generate property") return x.prop;
  if (place == "generate assertion") {
    return "    assert property (@(posedge clk) " + x.group + ");\n";
  }
  return "    always @(posedge clk) assert property (" + x.group + ");\n";
}

std::string OuterPlace(const std::string& place, const PlaceParts& x) {
  bool sequence = place.find("sequence") != std::string::npos;
  if (place.rfind("package", 0) == 0) {
    return "package pk;\n" + x.tasks + x.vars + (sequence ? x.seq : x.prop) +
           "endpackage\nmodule m; endmodule\n";
  }
  if (place.rfind("unit", 0) == 0) {
    return x.tasks + x.vars + (sequence ? x.seq : x.prop) +
           "module m; endmodule\n";
  }
  if (place.rfind("generate", 0) == 0) {
    return x.tasks + "module m;\n" + x.vars + "  if (1) begin : g\n" +
           GenerateItem(place, x) + "  end\nendmodule\n";
  }
  const std::string kBody =
      sequence ? "    sequence s; " + x.group + "; endsequence\n"
               : "    property p; " + x.group + "; endproperty\n";
  return x.tasks + "module m;\n" + x.vars + "  clocking cb @(posedge clk);\n" +
         kBody + "  endclocking\nendmodule\n";
}

std::string PassingPlace(const std::string& place, const std::string& call) {
  PlaceParts parts = PartsFor(call);
  for (const char* element : CheckedPlaces()) {
    if (place == element) return ElementPlace(place, parts);
  }
  return OuterPlace(place, parts);
}

void ExpectPlacesReportedAndAccepted(const std::vector<const char*>& places) {
  for (const char* place : places) {
    SCOPED_TRACE(place);
    ExpectPassingReported(PassingPlace(place, "tout(count)"), "tout(count)");
    ExpectPassingReported(PassingPlace(place, "tio(count)"), "tio(count)");
  }
}

void ExpectPlacesAccepted(const std::vector<const char*>& places) {
  for (const char* place : places) {
    std::string src = PassingPlace(place, "tin(count)");
    SCOPED_TRACE(src);
    ElabFixture f;
    ElaborateSrc(src, f);
    EXPECT_FALSE(f.diag.HasErrors());
  }
}

TEST(AttachedArgumentPassing, AnOutputActualInEachDesignElementIsReported) {
  ExpectPlacesReportedAndAccepted(CheckedPlaces());
}

TEST(AttachedArgumentPassing,
     DISABLED_AnOutputActualInEachOuterScopeIsReported) {
  ExpectPlacesReportedAndAccepted(OuterPlaces());
}

TEST(AttachedArgumentPassing, AnInputActualInEveryPlaceIsAccepted) {
  ExpectPlacesAccepted(CheckedPlaces());
  ExpectPlacesAccepted(OuterPlaces());
}

constexpr const char* kChandleReport =
    "a variable passed by value shall be of a type an assertion may use";

PlaceParts ChandleParts(const std::string& call) {
  PlaceParts parts = PartsFor(call);
  parts.tasks =
      "function automatic void fc(input chandle c); endfunction\n"
      "function automatic void fi(input int c); endfunction\n";
  parts.vars = "  bit clk, a;\n  int count;\n  chandle h;\n";
  parts.checker_vars = "  int count;\n  chandle h;\n";
  return parts;
}

std::string ChandlePlace(const std::string& place, const std::string& call) {
  PlaceParts parts = ChandleParts(call);
  for (const char* element : CheckedPlaces()) {
    if (place == element) return ElementPlace(place, parts);
  }
  return OuterPlace(place, parts);
}

std::string ChandleModule(const std::string& call) {
  return "module m;\n"
         "  bit clk, a;\n"
         "  int count;\n"
         "  chandle h;\n"
         "  chandle ha[2];\n"
         "  function automatic void fc(input chandle c); endfunction\n"
         "  function automatic void fn(chandle c); endfunction\n"
         "  function automatic void fi(input int c); endfunction\n"
         "  task automatic tc(input chandle c); endtask\n"
         "  task automatic ti(input int c); endtask\n"
         "  function automatic void fr(ref chandle c); endfunction\n"
         "  function automatic void fcr(const ref chandle c); endfunction\n"
         "  class C;\n"
         "    function void mf(input chandle c); endfunction\n"
         "    task mt(input chandle c); endtask\n"
         "    function void mfi(input int c); endfunction\n"
         "    task mti(input int c); endtask\n"
         "  endclass\n"
         "  C o = new;\n"
         "  sequence s; @(posedge clk) (a, " +
         call +
         ") ##1 a; endsequence\n"
         "endmodule\n";
}

void ExpectChandleReported(const std::string& src, const std::string& call) {
  SCOPED_TRACE(src);
  ElabFixture f;
  ElaborateSrc(src, f);
  uint32_t line = LineHolding(src, call);
  ASSERT_NE(line, 0u);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kChandleReport, line, "16.11"));
}

void ExpectChandleAccepted(const std::string& src) {
  SCOPED_TRACE(src);
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(AttachedByValueType, AChandleToAnInputOfEachSubroutineKindIsReported) {
  for (const char* call :
       {"fc(h)", "fn(h)", "tc(h)", "o.mf(h)", "o.mt(h)", "fc(ha[0])"}) {
    ExpectChandleReported(ChandleModule(call), call);
  }
}

TEST(AttachedByValueType, AnIntInputOrAChandleReferenceIsAccepted) {
  for (const char* call :
       {"fi(count)", "ti(count)", "o.mfi(count)", "o.mti(count)", "fr(h)",
        "fcr(h)", "$display(\"%d\", count)"}) {
    ExpectChandleAccepted(ChandleModule(call));
  }
}

TEST(AttachedByValueType, DISABLED_AChandleSystemTaskArgumentIsReported) {
  ExpectChandleReported(ChandleModule("$display(\"%p\", h)"),
                        "$display(\"%p\", h)");
}

TEST(AttachedByValueType, AChandleInEachDesignElementIsReported) {
  for (const char* place : CheckedPlaces()) {
    SCOPED_TRACE(place);
    ExpectChandleReported(ChandlePlace(place, "fc(h)"), "fc(h)");
  }
}

TEST(AttachedByValueType, DISABLED_AChandleInEachOuterScopeIsReported) {
  for (const char* place : OuterPlaces()) {
    SCOPED_TRACE(place);
    ExpectChandleReported(ChandlePlace(place, "fc(h)"), "fc(h)");
  }
}

TEST(AttachedByValueType, AnIntInEveryPlaceIsAccepted) {
  for (const auto& places : {CheckedPlaces(), OuterPlaces()}) {
    for (const char* place : places) {
      ExpectChandleAccepted(ChandlePlace(place, "fi(count)"));
    }
  }
}

constexpr const char* kAutomaticReport =
    "an automatic variable may not be passed by reference";

constexpr const char* kAutomaticCallees =
    "task automatic showr(ref int r); endtask\n"
    "task automatic showc(const ref int r); endtask\n"
    "task automatic showi(input int r); endtask\n"
    "function automatic void fr(ref int r); endfunction\n"
    "function automatic void fc(const ref int r); endfunction\n"
    "function automatic void fi(input int r); endfunction\n";

std::string AutomaticBlock(const std::string& head,
                           const std::string& statement) {
  return "  " + head +
         " begin\n"
         "    automatic int k = 1;\n"
         "    automatic int ka[2];\n"
         "    " +
         statement + "\n  end\n";
}

std::string AutomaticAssertion(const std::string& call) {
  return "assert property (@(posedge clk) (a, " + call + ") ##1 a);";
}

std::string AutomaticModule(const std::string& block) {
  return std::string(kAutomaticCallees) +
         "module m;\n"
         "  bit clk, a;\n"
         "  int count;\n"
         "  int arr[2];\n"
         "  class C; task tr(ref int r); endtask endclass\n"
         "  C h = new;\n"
         "  sequence sr(v); (a, showr(v)) ##1 a; endsequence\n"
         "  sequence si(v); (a, showi(v)) ##1 a; endsequence\n"
         "  property pr(v); @(posedge clk) (a, showr(v)) ##1 a; endproperty\n" +
         block + "endmodule\n";
}

void ExpectAutomaticReported(const std::string& src,
                             const std::string& marker) {
  SCOPED_TRACE(src);
  ElabFixture f;
  ElaborateSrc(src, f);
  uint32_t line = LineHolding(src, marker);
  ASSERT_NE(line, 0u);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kAutomaticReport, line, "16.11"));
}

void ExpectAutomaticAccepted(const std::string& src) {
  SCOPED_TRACE(src);
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(AttachedAutomatic, AnAutomaticByReferenceToEachCalleeIsReported) {
  for (const char* call :
       {"showc(k)", "showr(ka[0])", "h.tr(k)", "fr(k)", "fc(k)"}) {
    ExpectAutomaticReported(
        AutomaticModule(
            AutomaticBlock("always @(posedge clk)", AutomaticAssertion(call))),
        call);
  }
}

TEST(AttachedAutomatic, AnAutomaticByValueOrAStaticByReferenceIsAccepted) {
  for (const std::string& statement :
       {AutomaticAssertion("showi(k)"), AutomaticAssertion("showi(k + 1)"),
        AutomaticAssertion("showr(count)"), AutomaticAssertion("fi(k)"),
        std::string("assert property (@(posedge clk) si(k));"),
        "for (int i = 0; i < 2; i++) " + AutomaticAssertion("showi(i)")}) {
    ExpectAutomaticAccepted(
        AutomaticModule(AutomaticBlock("always @(posedge clk)", statement)));
  }
}

TEST(AttachedAutomatic, DISABLED_AStaticElementIndexedByAnAutomaticIsAccepted) {
  ExpectAutomaticAccepted(AutomaticModule(AutomaticBlock(
      "always @(posedge clk)", AutomaticAssertion("showr(arr[k])"))));
}

TEST(AttachedAutomatic, DISABLED_AForLoopVariableByReferenceIsReported) {
  for (const char* call : {"showr(i)", "showc(i)"}) {
    ExpectAutomaticReported(
        AutomaticModule(AutomaticBlock(
            "always @(posedge clk)",
            "for (int i = 0; i < 2; i++) " + AutomaticAssertion(call))),
        call);
  }
}

TEST(AttachedAutomatic,
     DISABLED_AnAutomaticReachingAReferenceThroughAnInstanceIsReported) {
  for (const char* instance : {"sr(k)", "pr(k)"}) {
    std::string marker = std::string("(posedge clk) ") + instance;
    ExpectAutomaticReported(
        AutomaticModule(AutomaticBlock("always @(posedge clk)",
                                       "assert property (@" + marker + ");")),
        marker);
  }
}

struct AutomaticPlace {
  const char* element;
  const char* head;
  bool functions_only;
};

const AutomaticPlace kAutomaticPlaces[] = {
    {"module", "initial", false},
    {"module", "always_ff @(posedge clk)", false},
    {"module", "always_comb", false},
    {"module", "always_latch", false},
    {"interface", "always @(posedge clk)", false},
    {"program", "initial", false},
    {"checker", "always_ff @(posedge clk)", true},
};

std::string AutomaticInElement(const AutomaticPlace& place,
                               const std::string& call) {
  std::string block = AutomaticBlock(place.head, AutomaticAssertion(call));
  std::string element = place.element;
  if (element == "module") return AutomaticModule(block);
  if (element == "checker") {
    return std::string(kAutomaticCallees) + "checker el(bit clk, bit a);\n" +
           block +
           "endchecker\nmodule m;\n  bit clk, a;\n  el u(clk, a);\n"
           "endmodule\n";
  }
  return std::string(kAutomaticCallees) + element + " el;\n  bit clk, a;\n" +
         block + "end" + element + "\nmodule m; el u(); endmodule\n";
}

TEST(AttachedAutomatic, AnAutomaticByReferenceInEachProcedureIsReported) {
  for (const AutomaticPlace& place : kAutomaticPlaces) {
    SCOPED_TRACE(place.head);
    for (const char* call :
         place.functions_only
             ? std::vector<const char*>{"fr(k)", "fc(k)"}
             : std::vector<const char*>{"showr(k)", "showc(k)"}) {
      ExpectAutomaticReported(AutomaticInElement(place, call), call);
    }
    ExpectAutomaticAccepted(
        AutomaticInElement(place, place.functions_only ? "fi(k)" : "showi(k)"));
  }
}

std::string AutomaticInGenerate(const std::string& generate,
                                const std::string& head,
                                const std::string& call) {
  return AutomaticModule("  " + generate + " begin : g\n" +
                         AutomaticBlock(head, AutomaticAssertion(call)) +
                         "  end\n");
}

const char* const kGenerateProcedures[][2] = {
    {"for (genvar gi = 0; gi < 1; gi++)", "always @(posedge clk)"},
    {"for (genvar gi = 0; gi < 1; gi++)", "initial"},
    {"if (1)", "always @(posedge clk)"},
};

TEST(AttachedAutomatic,
     DISABLED_AnAutomaticByReferenceInAGenerateBlockIsReported) {
  for (const auto& procedure : kGenerateProcedures) {
    SCOPED_TRACE(procedure[1]);
    for (const char* call : {"showr(k)", "showc(k)"}) {
      ExpectAutomaticReported(
          AutomaticInGenerate(procedure[0], procedure[1], call), call);
    }
  }
}

TEST(AttachedAutomatic, AnAutomaticByValueInAGenerateBlockIsAccepted) {
  for (const auto& procedure : kGenerateProcedures) {
    ExpectAutomaticAccepted(
        AutomaticInGenerate(procedure[0], procedure[1], "showi(k)"));
  }
}

constexpr const char* kUnassignedRead =
    "the local variable 'v' is referenced at a point where it is unassigned";

std::string LocalReadModule(const std::string& body) {
  return "module m;\n"
         "  bit clk, a, b;\n"
         "  function void show(int x); endfunction\n"
         "  sequence s;\n"
         "    int v;\n"
         "    @(posedge clk) " +
         body +
         ";\n"
         "  endsequence\n"
         "  c1: cover property (s);\n"
         "endmodule\n";
}

void ExpectUnassignedReadReported(const std::string& src) {
  SCOPED_TRACE(src);
  ElabFixture f;
  ElaborateSrc(src, f);
  uint32_t line = LineHolding(src, "show(v)");
  ASSERT_NE(line, 0u);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kUnassignedRead, line, "16.10"));
}

void ExpectReadAccepted(const std::string& src) {
  SCOPED_TRACE(src);
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(AttachedLocalRead, AReadAheadOfTheAssignmentInTheListIsReported) {
  ExpectUnassignedReadReported(LocalReadModule("(a, show(v), v = 1)"));
  ExpectReadAccepted(LocalReadModule("(a, v = 1, show(v))"));
}

TEST(AttachedLocalRead, AReadOfALocalOneOrOperandLeavesUnassignedIsReported) {
  ExpectUnassignedReadReported(
      LocalReadModule("((a, v = 1) or (a ##1 b), show(v))"));
  ExpectReadAccepted(
      LocalReadModule("((a, v = 1) or (a ##1 b, v = 2), show(v))"));
}

TEST(AttachedLocalRead,
     DISABLED_AReadOfALocalBothAndOrIntersectOperandsAssignIsReported) {
  for (const char* op : {"and", "intersect"}) {
    SCOPED_TRACE(op);
    ExpectUnassignedReadReported(LocalReadModule(std::string("((a, v = 1) ") +
                                                 op + " (a, v = 2), show(v))"));
  }
}

TEST(AttachedLocalRead,
     AReadOfALocalOneAndOrIntersectOperandAssignsIsAccepted) {
  for (const char* op : {"and", "intersect"}) {
    ExpectReadAccepted(LocalReadModule(std::string("((a, v = 1) ") + op +
                                       " (a ##0 b), show(v))"));
  }
}

std::string LocalReadSequence(const std::string& indent,
                              const std::string& clock,
                              const std::string& body) {
  return indent + "sequence s" + (clock.empty() ? "" : "(bit clk, bit a)") +
         ";\n" + indent + "  int v;\n" + indent + "  " + clock + body + ";\n" +
         indent + "endsequence\n";
}

std::string LocalReadIn(const std::string& place, const std::string& body) {
  const std::string kClocked = "@(posedge clk) ";
  const std::string kShow = "function void show(int x); endfunction\n";
  if (place == "interface" || place == "program") {
    return kShow + place + " el(input logic clk, a);\n" +
           LocalReadSequence("  ", "", kClocked + body) + "end" + place +
           "\nmodule m; bit clk, a; el u(clk, a); endmodule\n";
  }
  if (place == "checker") {
    return kShow + "checker el(bit clk, bit a);\n" +
           LocalReadSequence("  ", "", kClocked + body) +
           "endchecker\nmodule m; bit clk, a; el u(clk, a); endmodule\n";
  }
  if (place == "package") {
    return "package pk;\n  " + kShow + LocalReadSequence("  ", kClocked, body) +
           "endpackage\nmodule m; endmodule\n";
  }
  if (place == "unit") {
    return kShow + LocalReadSequence("", kClocked, body) +
           "module m; endmodule\n";
  }
  std::string inner =
      place == "generate"
          ? "  if (1) begin : g\n" +
                LocalReadSequence("    ", "", kClocked + body) + "  end\n"
          : "  clocking cb @(posedge clk);\n" +
                LocalReadSequence("    ", "", body) + "  endclocking\n";
  return kShow + "module m;\n  bit clk, a;\n" + inner + "endmodule\n";
}

TEST(AttachedLocalRead,
     AReadAheadOfTheAssignmentInEachDesignElementIsReported) {
  for (const char* place : {"interface", "program", "checker"}) {
    SCOPED_TRACE(place);
    ExpectUnassignedReadReported(LocalReadIn(place, "(a, show(v), v = 1)"));
  }
}

TEST(AttachedLocalRead,
     DISABLED_AReadAheadOfTheAssignmentInEachOuterScopeIsReported) {
  for (const char* place : {"package", "unit", "generate", "clocking"}) {
    SCOPED_TRACE(place);
    ExpectUnassignedReadReported(LocalReadIn(place, "(a, show(v), v = 1)"));
  }
}

TEST(AttachedLocalRead, AReadAfterTheAssignmentInEveryPlaceIsAccepted) {
  for (const char* place : {"interface", "program", "checker", "package",
                            "unit", "generate", "clocking"}) {
    SCOPED_TRACE(place);
    ExpectReadAccepted(LocalReadIn(place, "(a, v = 1, show(v))"));
  }
}

constexpr const char* kLocalByValueReport =
    "an actual holding a local variable shall be passed by value";

constexpr const char* kRefCallees =
    "task automatic showr(ref int r); endtask\n"
    "task automatic showc(const ref int r); endtask\n"
    "task automatic showi(input int r); endtask\n";

std::string LocalRefModule(const std::string& decl) {
  return std::string(kRefCallees) +
         "typedef struct { int f; } st_t;\n"
         "typedef int ia_t[2];\n"
         "task automatic shows(ref st_t r); endtask\n"
         "task automatic showa(ref int r[2]); endtask\n"
         "module m;\n"
         "  bit clk, a;\n"
         "  int arr[4];\n"
         "  int g;\n" +
         decl + "endmodule\n";
}

void ExpectLocalByValueReported(const std::string& src,
                                const std::string& call) {
  SCOPED_TRACE(src);
  ElabFixture f;
  ElaborateSrc(src, f);
  uint32_t line = LineHolding(src, call);
  ASSERT_NE(line, 0u);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kLocalByValueReport, line, "16.11"));
}

void ExpectLocalByValueAccepted(const std::string& src) {
  SCOPED_TRACE(src);
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
}

struct LocalRefForm {
  const char* decl;
  const char* call;
};

const LocalRefForm kReportedLocalRefForms[] = {
    {"  sequence s(local input int v); @(posedge clk) (a, showr(v)) ##1 a;"
     " endsequence\n",
     "showr(v)"},
    {"  property p(local input int v); @(posedge clk) (a, showr(v)) ##1 a;"
     " endproperty\n",
     "showr(v)"},
    {"  property p; int v; @(posedge clk) (a, v = 1, showr(v)) ##1 a;"
     " endproperty\n",
     "showr(v)"},
    {"  sequence s; st_t v; @(posedge clk) (a, v.f = 1, showr(v.f)) ##1 a;"
     " endsequence\n",
     "showr(v.f)"},
    {"  sequence s; ia_t v; @(posedge clk) (a, v[1] = 1, showr(v[1])) ##1 a;"
     " endsequence\n",
     "showr(v[1])"},
    {"  sequence s; int v; @(posedge clk) (a, v = 1, showr(arr[v])) ##1 a;"
     " endsequence\n",
     "showr(arr[v])"},
    {"  sequence s; st_t v; @(posedge clk) (a, v.f = 1, shows(v)) ##1 a;"
     " endsequence\n",
     "shows(v)"},
    {"  sequence s; int v; @(posedge clk) (a, v = 1, showc(v)) ##1 a;"
     " endsequence\n",
     "showc(v)"},
};

TEST(AttachedLocalByValue, ALocalInAReferenceActualOfEachFormIsReported) {
  for (const LocalRefForm& form : kReportedLocalRefForms) {
    ExpectLocalByValueReported(LocalRefModule(form.decl), form.call);
  }
}

TEST(AttachedLocalByValue, DISABLED_AnUnpackedArrayLocalByReferenceIsReported) {
  for (const LocalRefForm& form :
       {LocalRefForm{"  sequence s; int v[2]; @(posedge clk) (a, v[0] = 1,"
                     " showa(v)) ##1 a; endsequence\n",
                     "showa(v)"},
        LocalRefForm{"  sequence s; int v[2]; @(posedge clk) (a, v[1] = 1,"
                     " showr(v[1])) ##1 a; endsequence\n",
                     "showr(v[1])"}}) {
    ExpectLocalByValueReported(LocalRefModule(form.decl), form.call);
  }
}

TEST(AttachedLocalByValue, ALocalByValueOrANonLocalByReferenceIsAccepted) {
  for (const char* decl : {
           "  sequence s; int v; @(posedge clk) (a, v = 1, showi(v),"
           " showi(v + 1)) ##1 a; endsequence\n",
           "  sequence s(local input int v); @(posedge clk) (a, showi(v)) ##1 "
           "a;"
           " endsequence\n",
           "  property p; int v; @(posedge clk) (a, v = 1, showi(v)) ##1 a;"
           " endproperty\n",
           "  sequence s; int v[2]; @(posedge clk) (a, v[1] = 1, showi(v[1]))"
           " ##1 a; endsequence\n",
           "  sequence s; int v; @(posedge clk) (a, v = 1, showi(v), showr(g),"
           " showc(g)) ##1 a; endsequence\n",
       }) {
    ExpectLocalByValueAccepted(LocalRefModule(decl));
  }
}

std::string LocalRefDecl(const std::string& kind, const std::string& clock,
                         const std::string& call) {
  std::string body = clock + "(a, v = 1, " + call + ") ##1 a;";
  if (kind == "sequence")
    return "  sequence s; int v; " + body + " endsequence\n";
  return "  property p; int v; " + body + " endproperty\n";
}

std::string LocalRefElement(const std::string& place, const std::string& decl) {
  if (place == "checker") {
    return std::string(kRefCallees) + "checker el(logic clk, logic a);\n" +
           decl +
           "endchecker\nmodule m; logic clk, a; el u(clk, a); endmodule\n";
  }
  return std::string(kRefCallees) + place + " el(input logic clk, a);\n" +
         decl + "end" + place +
         "\nmodule m; logic clk, a; el u(clk, a); endmodule\n";
}

std::string LocalRefOuter(const std::string& place, const std::string& kind,
                          const std::string& call) {
  const std::string kClock = "@(posedge clk) ";
  if (place == "package") {
    return "package pk;\n" + std::string(kRefCallees) + "  bit clk, a;\n" +
           LocalRefDecl(kind, kClock, call) +
           "endpackage\nmodule m; endmodule\n";
  }
  if (place == "unit") {
    return std::string(kRefCallees) + "bit clk, a;\n" +
           LocalRefDecl(kind, kClock, call) + "module m; endmodule\n";
  }
  std::string inner;
  if (place == "clocking") {
    inner = "  clocking cb @(posedge clk);\n" + LocalRefDecl(kind, "", call) +
            "  endclocking\n";
  } else {
    inner = (place == "for generate"
                 ? "  for (genvar i = 0; i < 1; i++) begin : g\n"
                 : "  if (1) begin : g\n") +
            LocalRefDecl(kind, kClock, call) + "  end\n";
  }
  return std::string(kRefCallees) + "module m;\n  bit clk, a;\n" + inner +
         "endmodule\n";
}

const char* const kLocalRefElements[] = {"interface", "program", "checker"};
const char* const kLocalRefOuters[] = {"package", "unit", "if generate",
                                       "for generate", "clocking"};
const char* const kLocalRefKinds[] = {"sequence", "property"};

TEST(AttachedLocalByValue, ALocalByReferenceInEachDesignElementIsReported) {
  for (const char* place : kLocalRefElements) {
    for (const char* kind : kLocalRefKinds) {
      SCOPED_TRACE(std::string(place) + " " + kind);
      ExpectLocalByValueReported(
          LocalRefElement(place,
                          LocalRefDecl(kind, "@(posedge clk) ", "showr(v)")),
          "showr(v)");
    }
  }
}

TEST(AttachedLocalByValue,
     DISABLED_ALocalByReferenceInEachOuterScopeIsReported) {
  for (const char* place : kLocalRefOuters) {
    for (const char* kind : kLocalRefKinds) {
      SCOPED_TRACE(std::string(place) + " " + kind);
      ExpectLocalByValueReported(LocalRefOuter(place, kind, "showr(v)"),
                                 "showr(v)");
    }
  }
}

TEST(AttachedLocalByValue, ALocalByValueInEveryPlaceIsAccepted) {
  for (const char* kind : kLocalRefKinds) {
    for (const char* place : kLocalRefElements) {
      ExpectLocalByValueAccepted(LocalRefElement(
          place, LocalRefDecl(kind, "@(posedge clk) ", "showi(v)")));
    }
    for (const char* place : kLocalRefOuters) {
      ExpectLocalByValueAccepted(LocalRefOuter(place, kind, "showi(v)"));
    }
  }
}

}  // namespace
