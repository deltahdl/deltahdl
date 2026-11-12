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

const char kChandleRef[] =
    "concurrent assertion expression references chandle variable";

const char kChandleForm[] = "h != null";
const char kLogicForm[] = "g";

std::string WithForm(std::string text, const std::string& form) {
  for (size_t at = text.find("@@"); at != std::string::npos;
       at = text.find("@@", at + form.size())) {
    text.replace(at, 2, form);
  }
  return text;
}

std::string ChandleBench(const std::string& items,
                         const std::string& outside = "") {
  return outside +
         "module top;\n"
         "  logic clk = 0, a = 1, g = 1;\n"
         "  chandle h;\n"
         "  sequence sa(x); @(posedge clk) x; endsequence\n"
         "  property pa(x); @(posedge clk) x; endproperty\n"
         "  " +
         items + "\nendmodule\n";
}

std::string StatementOf(const std::string& place) {
  return place.substr(place.rfind('\n') + 1);
}

void ExpectChandleReported(const std::string& place, const std::string& form,
                           const std::string& outside = "") {
  const std::string kSrc = WithForm(ChandleBench(place, outside), form);
  ElabFixture f;
  Elaborate(kSrc, f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(), kChandleRef,
      LineHolding(kSrc, WithForm(StatementOf(place), form)), "16.6"))
      << kSrc;
}

void ExpectChandleAccepted(const std::string& place, const std::string& form,
                           const std::string& outside = "") {
  const std::string kSrc = WithForm(ChandleBench(place, outside), form);
  ElabFixture f;
  auto* design = Elaborate(kSrc, f);
  ASSERT_NE(design, nullptr) << kSrc;
  EXPECT_FALSE(f.has_errors) << kSrc;
}

const char* const kReportedPlaces[] = {
    "assert property (@(posedge clk) @@);",
    "assume property (@(posedge clk) @@);",
    "cover property (@(posedge clk) @@);",
    "cover sequence (@(posedge clk) @@);",
    "assert property (@(posedge clk) not (@@));",
    "property q; @(posedge clk) @@; endproperty\n  assert property (q);",
    "assert property (sa(@@));",
    "assert property (pa(@@));",
    "if (1) begin : gb assert property (@(posedge clk) @@); end",
};

const char* const kUnreportedPlaces[] = {
    "restrict property (@(posedge clk) @@);",
    "assert property (@(posedge clk) a ##1 @@);",
    "assert property (@(posedge clk) a and @@);",
    "assert property (@(posedge clk) a or @@);",
    "assert property (@(posedge clk) (a ##1 a) intersect (@@ ##1 a));",
    "assert property (@(posedge clk) @@ within (a ##1 a));",
    "assert property (@(posedge clk) @@ throughout (a ##1 a));",
    "assert property (@(posedge clk) @@ |-> a);",
    "assert property (@(posedge clk) a |-> @@);",
    "assert property (@(posedge clk) @@ |=> a);",
    "assert property (@(posedge clk) a |=> @@);",
    "sequence s; @(posedge clk) @@; endsequence\n  assert property (s);",
    "let l = @@;\n  assert property (@(posedge clk) l);",
    "assert property (@(posedge clk) disable iff (@@) a);",
    "default disable iff (@@);\n  assert property (@(posedge clk) a);",
    "assert property (@(posedge clk iff @@) a);",
    "always @(posedge clk) assert property (@@);",
    "initial assert property (@(posedge clk) @@);",
};

TEST(ChandleInAssertion, EveryPlaceAcceptsAnOrdinaryVariable) {
  for (const char* place : kReportedPlaces) {
    ExpectChandleAccepted(place, kLogicForm);
  }
  for (const char* place : kUnreportedPlaces) {
    ExpectChandleAccepted(place, kLogicForm);
  }
}

TEST(ChandleInAssertion, TheDirectAndInstancedPlacesReportAChandle) {
  for (const char* place : kReportedPlaces) {
    ExpectChandleReported(place, kChandleForm);
  }
}

TEST(ChandleInAssertion, DISABLED_EveryOtherPlaceReportsAChandle) {
  for (const char* place : kUnreportedPlaces) {
    ExpectChandleReported(place, kChandleForm);
  }
}

TEST(ChandleInAssertion, ASampledValueFunctionOfAChandleIsReported) {
  const char kPlace[] = "assert property (@(posedge clk) @@);";
  for (const char* form : {"$past(h) != null", "$stable(h)"}) {
    ExpectChandleReported(kPlace, form);
  }
  for (const char* form : {"$past(g)", "$stable(g)"}) {
    ExpectChandleAccepted(kPlace, form);
  }
}

TEST(ChandleInAssertion, AChandleInTheActionBlockIsAccepted) {
  ExpectChandleAccepted(
      "assert property (@(posedge clk) a) else $display(\"%0d\", @@);",
      kChandleForm);
}

std::string ChandleUnit(const char* kind) {
  return std::string(kind) +
         " u_unit(input logic clk);\n"
         "  logic g = 1;\n"
         "  chandle h;\n"
         "  assert property (@(posedge clk) @@);\n"
         "end" +
         kind + "\n";
}

const char kChandleChecker[] =
    "checker u_unit(logic clk);\n"
    "  logic g = 1;\n"
    "  chandle h;\n"
    "  assert property (@(posedge clk) @@);\n"
    "endchecker\n";

TEST(ChandleInAssertion, EveryUnitReportsAChandleBesideAVariable) {
  for (const std::string& unit :
       {ChandleUnit("interface"), ChandleUnit("program"),
        std::string(kChandleChecker)}) {
    const std::string kSrc =
        WithForm(ChandleBench("u_unit u(clk);", unit), kChandleForm);
    ElabFixture f;
    Elaborate(kSrc, f);
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(), kChandleRef,
        LineHolding(kSrc, "assert property (@(posedge clk) h != null);"),
        "16.6"))
        << kSrc;
    ExpectChandleAccepted("u_unit u(clk);", kLogicForm, unit);
  }
}

const char kSideEffect[] = "is a side effect";

std::string SideBench(const std::string& items,
                      const std::string& outside = "") {
  return "typedef struct {int f;} t_s;\n" + outside +
         "module top;\n"
         "  logic clk = 0, a = 1;\n"
         "  int n; int v[2]; t_s s;\n"
         "  function void f(); endfunction\n"
         "  " +
         items + "\nendmodule\n";
}

int ReportsAt(const std::vector<Diagnostic>& diags, const char* message,
              uint32_t line) {
  int count = 0;
  for (const auto& diag : diags) {
    if (diag.severity == DiagSeverity::kError &&
        diag.message.find(message) != std::string::npos &&
        diag.loc.line == line && diag.subclause == "16.6") {
      ++count;
    }
  }
  return count;
}

void ExpectReportedOnce(const char* message, const std::string& marked,
                        const std::string& form, uint32_t line) {
  const std::string kSrc = WithForm(marked, form);
  ElabFixture f;
  Elaborate(kSrc, f);
  EXPECT_EQ(ReportsAt(f.diag.Diagnostics(), message, line), 1) << kSrc;
}

void ExpectSideEffectOnce(const std::string& marked, const std::string& form) {
  ExpectReportedOnce(kSideEffect, marked, form, LineHolding(marked, "@@"));
}

void ExpectNoSideEffect(const std::string& marked, const std::string& form) {
  const std::string kSrc = WithForm(marked, form);
  ElabFixture f;
  auto* design = Elaborate(kSrc, f);
  ASSERT_NE(design, nullptr) << kSrc;
  EXPECT_FALSE(f.has_errors) << kSrc;
}

const char kBoolean[] = "assert property (@(posedge clk) @@);";

TEST(AssertionSideEffect, ABooleanWithoutAWriteIsAccepted) {
  for (const char* form : {"n < 10", "n == 3", "v[0] < 10", "s.f == 1"}) {
    ExpectNoSideEffect(SideBench(kBoolean), form);
  }
}

TEST(AssertionSideEffect, EveryIncrementOrDecrementInABooleanIsReported) {
  for (const char* form :
       {"n++ < 10", "++n < 10", "n-- < 10", "--n < 10", "v[0]++ < 10"}) {
    ExpectSideEffectOnce(SideBench(kBoolean), form);
  }
}

TEST(AssertionSideEffect, DISABLED_EveryAssignmentInABooleanIsReported) {
  for (const char* form :
       {"(n = 3) == 3", "(n += 1) > 0", "(n -= 1) > 0", "(n *= 2) > 0",
        "(n /= 2) > 0", "(n %= 2) > 0", "(n &= 1) > 0", "(n |= 1) > 0",
        "(n ^= 1) > 0", "(n <<= 1) > 0", "(n >>= 1) > 0", "(n <<<= 1) > 0",
        "(n >>>= 1) > 0", "(s.f = 1) == 1", "(v[0] = 1) == 1"}) {
    ExpectSideEffectOnce(SideBench(kBoolean), form);
  }
}

const char kLocalProperty[] =
    "property plv; int x; int w[2]; t_s t;\n"
    "    @(posedge clk) @@;\n"
    "  endproperty\n"
    "  assert property (plv);";

TEST(AssertionSideEffect, EveryMatchItemWritingALocalIsAccepted) {
  for (const char* form : {"(a, x = 0)",
                           "(a, x = 0, x++)",
                           "(a, x = 0, ++x)",
                           "(a, x = 0, x--)",
                           "(a, x = 0, --x)",
                           "(a, x = 0, x += 2)",
                           "(a, x = 0, x -= 2)",
                           "(a, x = 0, x *= 2)",
                           "(a, x = 0, x /= 2)",
                           "(a, x = 0, x %= 2)",
                           "(a, x = 0, x &= 1)",
                           "(a, x = 0, x |= 1)",
                           "(a, x = 0, x ^= 1)",
                           "(a, x = 0, x <<= 1)",
                           "(a, x = 0, x >>= 1)",
                           "(a, x = 0, x <<<= 1)",
                           "(a, x = 0, x >>>= 1)",
                           "(a, w = '{0, 0}, w[1] = 1)",
                           "(a, t = '{f: 0}, t.f = 1)",
                           "(a, x = 0) ##1 (a, x++)",
                           "(a, f())"}) {
    ExpectNoSideEffect(SideBench(kLocalProperty), form);
  }
}

TEST(AssertionSideEffect,
     DISABLED_AnIncrementOfALocalOutsideAMatchItemIsReported) {
  ExpectSideEffectOnce(SideBench(kLocalProperty), "(a, x = 0) ##1 x++ < 10");
}

TEST(AssertionSideEffect,
     DISABLED_AnAssignmentOfALocalOutsideAMatchItemIsReported) {
  for (const char* form : {"(x = 1) ##1 a", "(a, x = 0) ##1 (x += 1) > 0"}) {
    ExpectSideEffectOnce(SideBench(kLocalProperty), form);
  }
}

TEST(AssertionSideEffect, DISABLED_AMatchItemWritingAModuleVariableIsReported) {
  for (const char* form : {"(a, n = 1)", "(a, n++)", "(a, --n)", "(a, n += 1)",
                           "(a, v[0] = 1)", "(a, s.f = 1)"}) {
    ExpectSideEffectOnce(SideBench(kLocalProperty), form);
  }
}

const char kFormalSequences[] =
    "sequence su(u); @(posedge clk) (a, u = 0, @@); endsequence\n"
    "  sequence sf(local inout int w); @(posedge clk) (a, w = 0, @@);\n"
    "  endsequence\n"
    "  property pl; int y; su(y); endproperty\n"
    "  property pf; int y; @(posedge clk) (1, y = 0) ##0 sf(y); endproperty\n"
    "  ";

std::string OnTarget(const char* form, const char* target) {
  std::string out;
  for (const char* c = form; *c != '\0'; ++c) {
    if (*c == '$') {
      out.append(target);
    } else {
      out.push_back(*c);
    }
  }
  return out;
}

TEST(AssertionSideEffect, EveryMatchItemOnALocalThroughAFormalIsAccepted) {
  for (const char* form :
       {"$ = 1", "$++", "++$", "$--", "--$", "$ += 2", "$ -= 2", "$ *= 2",
        "$ /= 2", "$ %= 2", "$ &= 1", "$ |= 1", "$ ^= 1", "$ <<= 1", "$ >>= 1",
        "$ <<<= 1", "$ >>>= 1"}) {
    const std::string kSrc =
        SideBench(std::string(kFormalSequences) +
                  "assert property (pl);\n  assert property (pf);");
    const std::size_t kAt = kSrc.find("@@");
    ExpectNoSideEffect(
        kSrc.substr(0, kAt) + OnTarget(form, "u") + kSrc.substr(kAt + 2),
        OnTarget(form, "w"));
  }
}

TEST(AssertionSideEffect,
     DISABLED_AMatchItemOnAModuleVariableThroughAFormalIsReported) {
  ExpectSideEffectOnce(SideBench("sequence su(u); @(posedge clk) (a, u = 1); "
                                 "endsequence\n  cover property (su(@@));"),
                       "n");
}

const char* const kSidePlaces[] = {
    "assert property (@(posedge clk) a ##1 @@);",
    "assert property (@(posedge clk) a |-> @@);",
    "sequence sq; @(posedge clk) @@; endsequence\n  cover property (sq);",
    ("property pq; @(posedge clk) @@; endproperty\n"
     "  assert property (pq);\n  cover property (pq);"),
    "assert property (@(posedge clk) disable iff (@@) a);",
    ("default disable iff (@@);\n  assert property (@(posedge clk) a);\n"
     "  cover property (@(posedge clk) a);"),
    "always @(posedge clk) assert property (@@);",
    "if (1) begin : g assert property (@(posedge clk) @@); end",
    ("for (genvar j = 0; j < 1; j++) begin : lg\n"
     "    assert property (@(posedge clk) @@);\n  end"),
};

TEST(AssertionSideEffect, EveryPlaceAcceptsABooleanWithoutAWrite) {
  for (const char* place : kSidePlaces) {
    ExpectNoSideEffect(SideBench(place), "n < 10");
  }
}

TEST(AssertionSideEffect, DISABLED_EveryPlaceReportsAnIncrementOnce) {
  for (const char* place : kSidePlaces) {
    ExpectSideEffectOnce(SideBench(place), "n++ < 10");
  }
}

TEST(AssertionSideEffect, DISABLED_EveryPlaceReportsAnAssignmentOnce) {
  for (const char* place : kSidePlaces) {
    ExpectSideEffectOnce(SideBench(place), "(n = 3) == 3");
  }
}

std::string SideUnit(const char* kind) {
  return std::string(kind) +
         " u_unit(input logic clk, input logic a);\n"
         "  int n;\n"
         "  sequence sl; int x; @(posedge clk) (a, x = 0, x++); endsequence\n"
         "  cover property (sl);\n"
         "  assert property (@(posedge clk) @@);\n"
         "end" +
         kind + "\n";
}

const char kSideChecker[] =
    "checker u_unit(logic clk, logic a);\n"
    "  int n;\n"
    "  sequence sl; int x; @(posedge clk) (a, x = 0, x++); endsequence\n"
    "  cover property (sl);\n"
    "  assert property (@(posedge clk) @@);\n"
    "endchecker\n";

const char kPackageSequence[] =
    "package pk;\n"
    "  logic pclk = 0; int pn;\n"
    "  sequence ps; @(posedge pclk) @@; endsequence\n"
    "  sequence pl; int x; @(posedge pclk) (1, x = 0, x++); endsequence\n"
    "endpackage\n";

const char kUnitSequence[] =
    "logic uclk = 0; int un;\n"
    "sequence us; @(posedge uclk) @@; endsequence\n"
    "sequence ul; int x; @(posedge uclk) (1, x = 0, x++); endsequence\n";

const char kDeclaredUse[] =
    "cover property (pk::ps);\n  cover property (us);\n"
    "  cover property (pk::pl);\n  cover property (ul);";

void ExpectEveryUnit(const char* form, bool reported) {
  for (const std::string& unit : {SideUnit("interface"), SideUnit("program"),
                                  std::string(kSideChecker)}) {
    const std::string kMarked = SideBench("u_unit u(clk, a);", unit);
    if (reported) {
      ExpectSideEffectOnce(kMarked, form);
    } else {
      ExpectNoSideEffect(kMarked, form);
    }
  }
}

TEST(AssertionSideEffect, EveryUnitAcceptsALocalMatchItem) {
  ExpectEveryUnit("n < 10", false);
  for (const char* place :
       {"if (1) begin : g\n    @@\n  end",
        "for (genvar j = 0; j < 1; j++) begin : lg\n    @@\n  end"}) {
    ExpectNoSideEffect(SideBench(place),
                       "sequence sl; int x; @(posedge clk) (a, x = 0, x++); "
                       "endsequence\n    cover property (sl);");
  }
  ExpectNoSideEffect(
      SideBench(kDeclaredUse, WithForm(kPackageSequence, "pn < 10") +
                                  WithForm(kUnitSequence, "un < 10")),
      "");
}

TEST(AssertionSideEffect, EveryUnitReportsAnIncrement) {
  ExpectEveryUnit("n++ < 10", true);
}

TEST(AssertionSideEffect, DISABLED_EveryUnitReportsAnAssignment) {
  ExpectEveryUnit("(n = 3) == 3", true);
}

TEST(AssertionSideEffect, DISABLED_APackageOrUnitSequenceReportsAnIncrement) {
  ExpectSideEffectOnce(
      SideBench(kDeclaredUse, kPackageSequence + WithForm(kUnitSequence, "1")),
      "pn++ < 10");
  ExpectSideEffectOnce(
      SideBench(kDeclaredUse, WithForm(kPackageSequence, "1") + kUnitSequence),
      "un++ < 10");
}

const char kWritingArgument[] =
    "has an output, inout or ref argument and cannot be called in a concurrent "
    "assertion";

std::string FnBench(const std::string& items, const std::string& outside = "") {
  return outside +
         "module top;\n"
         "  logic clk = 0, a = 1;\n"
         "  int cnt;\n"
         "  function automatic bit fo(output int n); n = 0; return 1; "
         "endfunction\n"
         "  function automatic bit fio(inout int n); return n > 0; "
         "endfunction\n"
         "  function automatic bit fr(ref int n); return n > 0; endfunction\n"
         "  function automatic bit frs(ref static int n); return n > 0; "
         "endfunction\n"
         "  function automatic bit fin(input int n); return n > 0; "
         "endfunction\n"
         "  function automatic bit fcr(const ref int n); return n > 0; "
         "endfunction\n"
         "  function automatic bit fcrs(const ref static int n); return n > 0; "
         "endfunction\n"
         "  function automatic bit fi(bit b); return b; endfunction\n"
         "  " +
         items + "\nendmodule\n";
}

void ExpectWritingArgumentOnce(const std::string& marked,
                               const std::string& form) {
  ExpectReportedOnce(kWritingArgument, marked, form, LineHolding(marked, "@@"));
}

TEST(AssertionFunctionArgument, EveryWritingArgumentKindIsReported) {
  for (const char* form : {"fo(cnt)", "fio(cnt)", "fr(cnt)", "frs(cnt)"}) {
    ExpectWritingArgumentOnce(FnBench(kBoolean), form);
  }
}

TEST(AssertionFunctionArgument, EveryReadOnlyArgumentKindIsAccepted) {
  for (const char* form : {"fin(cnt)", "fcr(cnt)", "fcrs(cnt)"}) {
    ExpectNoSideEffect(FnBench(kBoolean), form);
  }
}

const char* const kFnPlaces[] = {
    "assume property (@(posedge clk) @@);",
    "cover property (@(posedge clk) @@);",
    "cover sequence (@(posedge clk) @@);",
    "restrict property (@(posedge clk) @@);",
    "initial expect (@(posedge clk) @@);",
    "sequence sq; @(posedge clk) @@; endsequence\n  cover property (sq);",
    "assert property (@(posedge clk) a ##1 @@);",
    "assert property (@(posedge clk) a |-> @@);",
    "assert property (@(posedge clk) disable iff (@@) a);",
    "assert property (@(posedge @@) a);",
    ("sequence sx(x); @(posedge clk) x; endsequence\n"
     "  assert property (sx(@@));"),
    "assert property (@(posedge clk) $past(@@));",
    "assert property (@(posedge clk) fi(@@));",
    "always @(posedge clk) assert property (@@);",
};

const char* const kFnRepeatedPlaces[] = {
    ("property pq; @(posedge clk) @@; endproperty\n"
     "  assert property (pq);\n  cover property (pq);"),
    ("default disable iff (@@);\n  assert property (@(posedge clk) a);\n"
     "  cover property (@(posedge clk) a);"),
};

const char* const kFnGeneratePlaces[] = {
    "if (1) begin : g assert property (@(posedge clk) @@); end",
    ("for (genvar j = 0; j < 1; j++) begin : lg\n"
     "    assert property (@(posedge clk) @@);\n  end"),
};

TEST(AssertionFunctionArgument, EveryPlaceAcceptsAConstRefArgument) {
  for (const char* place : kFnPlaces) {
    ExpectNoSideEffect(FnBench(place), "fcr(cnt)");
  }
  for (const char* place : kFnRepeatedPlaces) {
    ExpectNoSideEffect(FnBench(place), "fcr(cnt)");
  }
  for (const char* place : kFnGeneratePlaces) {
    ExpectNoSideEffect(FnBench(place), "fcr(cnt)");
  }
}

TEST(AssertionFunctionArgument, EveryDirectiveAndPlaceReportsAnOutputArgument) {
  for (const char* place : kFnPlaces) {
    ExpectWritingArgumentOnce(FnBench(place), "fo(cnt)");
  }
}

TEST(AssertionFunctionArgument,
     DISABLED_ANamedPropertyOrDefaultDisableReportsItOnce) {
  for (const char* place : kFnRepeatedPlaces) {
    ExpectWritingArgumentOnce(FnBench(place), "fo(cnt)");
  }
}

TEST(AssertionFunctionArgument,
     DISABLED_AGenerateBlockReportsAnOutputArgument) {
  for (const char* place : kFnGeneratePlaces) {
    ExpectWritingArgumentOnce(FnBench(place), "fo(cnt)");
  }
}

const char kLetUse[] = "assert property (@(posedge clk) l(cnt));";

TEST(AssertionFunctionArgument, ALetCallingAConstRefFunctionIsAccepted) {
  ExpectNoSideEffect(FnBench(std::string("let l(x) = @@;\n  ") + kLetUse),
                     "fcr(x)");
}

TEST(AssertionFunctionArgument,
     DISABLED_ALetCallingAnOutputFunctionIsReported) {
  const std::string kMarked =
      FnBench(std::string("let l(x) = @@;\n  ") + kLetUse);
  ExpectReportedOnce(kWritingArgument, kMarked, "fo(x)",
                     LineHolding(kMarked, kLetUse));
}

const char kFnPackage[] =
    "package pk;\n"
    "  function automatic bit pf(output int n); n = 0; return 1; endfunction\n"
    "  function automatic bit pc(const ref int n); return n > 0; endfunction\n"
    "  checker pck(logic clk);\n"
    "    int c;\n"
    "    assert property (@(posedge clk) @@);\n"
    "  endchecker\n"
    "endpackage\n"
    "class C;\n"
    "  static function bit sf(ref int n); return n > 0; endfunction\n"
    "  static function bit sc(const ref int n); return n > 0; endfunction\n"
    "endclass\n";

TEST(AssertionFunctionArgument,
     APackageOrClassScopeReadOnlyFunctionIsAccepted) {
  const std::string kPackage = WithForm(kFnPackage, "pc(c)");
  for (const char* call : {"pk::pc(cnt)", "C::sc(cnt)"}) {
    ExpectNoSideEffect(FnBench(kBoolean, kPackage), call);
  }
  ExpectNoSideEffect(
      FnBench("import pk::*;\n  assert property (@(posedge clk) pc(cnt));\n"
              "  pk::pck k(clk);",
              kPackage),
      "");
}

TEST(AssertionFunctionArgument,
     DISABLED_APackageOrClassScopeWritingFunctionIsReported) {
  const std::string kPackage = WithForm(kFnPackage, "pc(c)");
  for (const char* call : {"pk::pf(cnt)", "C::sf(cnt)"}) {
    ExpectWritingArgumentOnce(FnBench(kBoolean, kPackage), call);
  }
  ExpectWritingArgumentOnce(
      FnBench(std::string("import pk::*;\n  ") + kBoolean, kPackage),
      "pf(cnt)");
  const std::string kChecker = FnBench("pk::pck k(clk);", kFnPackage);
  ExpectWritingArgumentOnce(kChecker, "pf(c)");
}

std::string FnUnit(const char* kind) {
  const std::string kEnd = std::string(kind) == "checker" ? "" : "input ";
  return std::string(kind) + " u_unit(" + kEnd +
         "logic clk);\n"
         "  int cnt;\n"
         "  function automatic bit fo(output int n); n = 0; return 1; "
         "endfunction\n"
         "  function automatic bit fcr(const ref int n); return n > 0; "
         "endfunction\n"
         "  assert property (@(posedge clk) @@);\n"
         "end" +
         kind + "\n";
}

TEST(AssertionFunctionArgument, EveryUnitReportsAnOutputArgument) {
  for (const char* kind : {"interface", "program", "checker"}) {
    const std::string kMarked = FnBench("u_unit u(clk);", FnUnit(kind));
    ExpectWritingArgumentOnce(kMarked, "fo(cnt)");
    ExpectNoSideEffect(kMarked, "fcr(cnt)");
  }
}

}  // namespace
