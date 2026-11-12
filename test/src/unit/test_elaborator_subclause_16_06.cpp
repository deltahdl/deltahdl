#include <gtest/gtest.h>

#include <cstddef>
#include <initializer_list>
#include <string>

#include "elaborator/concurrent_assertion_expr.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ConcurrentAssertionBooleanExpr, ChandleInAssertPropertyRejectedEndToEnd) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic clk;\n"
      "  chandle h;\n"
      "  assert property (@(posedge clk) h != null);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "concurrent assertion expression references chandle", 4, "16.6"));
}

TEST(ConcurrentAssertionBooleanExpr, OrdinaryVariableInAssertPropertyAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic clk, a;\n"
      "  assert property (@(posedge clk) a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConcurrentAssertionBooleanExpr, UnreferencedChandleDoesNotTripAssertRule) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic clk, a;\n"
      "  chandle h;\n"
      "  assert property (@(posedge clk) a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConcurrentAssertionBooleanExpr, NonStaticClassPropertyRejectedEndToEnd) {
  ElabFixture f;
  Elaborate(
      "class H; bit v = 1; endclass\n"
      "module m;\n"
      "  logic clk;\n"
      "  H h = new;\n"
      "  assert property (@(posedge clk) $past(h.v) || h.v);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "concurrent assertion expression references "
                            "non-static class member \"h.v\"",
                            5, "16.6"));
}

TEST(ConcurrentAssertionBooleanExpr, NonStaticClassMethodRejectedEndToEnd) {
  ElabFixture f;
  Elaborate(
      "class H;\n"
      "  bit v;\n"
      "  function bit get(); return v; endfunction\n"
      "endclass\n"
      "module m;\n"
      "  logic clk;\n"
      "  H h = new;\n"
      "  assert property (@(posedge clk) h.get());\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "concurrent assertion expression references "
                            "non-static class member \"h.get\"",
                            8, "16.6"));
}

TEST(ConcurrentAssertionBooleanExpr, StaticClassPropertyAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "class B; static bit s; endclass\n"
      "class H extends B; static bit v; endclass\n"
      "module m;\n"
      "  logic clk;\n"
      "  H h = new;\n"
      "  assert property (@(posedge clk) h.v || H::v || h.s);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConcurrentAssertionBooleanExpr,
     OverallResultMustBeCastCompatibleWithIntegral) {
  EXPECT_TRUE(ConcurrentAssertionExprTypeIsAcceptable(true));
  EXPECT_FALSE(ConcurrentAssertionExprTypeIsAcceptable(false));
}

TEST(ConcurrentAssertionBooleanExpr, SubexpressionTypeIsExemptFromRule) {
  EXPECT_TRUE(ConcurrentAssertionSubexprTypeIsExempt());
}

TEST(ConcurrentAssertionBooleanExpr,
     AutomaticVariableOnlyReferenceableInProceduralConcurrentAssertions) {
  EXPECT_TRUE(AutomaticVariableReferenceAllowed(true));
  EXPECT_FALSE(AutomaticVariableReferenceAllowed(false));
}

TEST(ConcurrentAssertionBooleanExpr, NonStaticClassMemberReferenceIsForbidden) {
  EXPECT_FALSE(NonStaticClassMemberReferenceAllowed());
}

TEST(ConcurrentAssertionBooleanExpr, ChandleReferenceIsForbidden) {
  EXPECT_FALSE(ChandleVariableReferenceAllowed());
}

TEST(ConcurrentAssertionBooleanExpr,
     SideEffectsAllowedOnlyInSequenceMatchItemWithLocalLvalue) {
  EXPECT_TRUE(SideEffectAllowed(true, true));
  EXPECT_FALSE(SideEffectAllowed(true, false));
  EXPECT_FALSE(SideEffectAllowed(false, true));
  EXPECT_FALSE(SideEffectAllowed(false, false));
}

TEST(ConcurrentAssertionBooleanExpr,
     FunctionArgKindFiltersOutputInoutRefAllowsConstRef) {
  EXPECT_TRUE(FunctionArgKindAllowedInAssertionExpr(FunctionArgKind::kInput));
  EXPECT_TRUE(
      FunctionArgKindAllowedInAssertionExpr(FunctionArgKind::kConstRef));
  EXPECT_FALSE(FunctionArgKindAllowedInAssertionExpr(FunctionArgKind::kOutput));
  EXPECT_FALSE(FunctionArgKindAllowedInAssertionExpr(FunctionArgKind::kInout));
  EXPECT_FALSE(FunctionArgKindAllowedInAssertionExpr(FunctionArgKind::kRef));
}

TEST(ConcurrentAssertionBooleanExpr,
     FunctionMustBeAutomaticOrStatelessAndHaveNoSideEffects) {
  EXPECT_TRUE(FunctionEligibleInAssertionExpr(true, false, true));
  EXPECT_TRUE(FunctionEligibleInAssertionExpr(false, true, true));
  EXPECT_TRUE(FunctionEligibleInAssertionExpr(true, true, true));
  EXPECT_FALSE(FunctionEligibleInAssertionExpr(false, false, true));
  EXPECT_FALSE(FunctionEligibleInAssertionExpr(true, true, false));
  EXPECT_FALSE(FunctionEligibleInAssertionExpr(true, false, false));
  EXPECT_FALSE(FunctionEligibleInAssertionExpr(false, true, false));
  EXPECT_FALSE(FunctionEligibleInAssertionExpr(false, false, false));
}

TEST(ConcurrentAssertionBooleanExpr,
     DisableConditionAllowsTriggeredAndOrdinaryButForbidsLocalAndMatched) {
  EXPECT_TRUE(
      DisableConditionRefAllowed(DisableConditionRefKind::kOrdinaryVariable));
  EXPECT_TRUE(
      DisableConditionRefAllowed(DisableConditionRefKind::kTriggeredMethod));
  EXPECT_FALSE(
      DisableConditionRefAllowed(DisableConditionRefKind::kLocalVariable));
  EXPECT_FALSE(
      DisableConditionRefAllowed(DisableConditionRefKind::kMatchedMethod));
}

TEST(AssertionFunctionCalls, AFunctionWritingAnArgumentBackIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a;\n"
      "  int seen;\n"
      "  function automatic bit peek(input bit x, output int n);\n"
      "    n = 1;\n"
      "    return x;\n"
      "  endfunction\n"
      "  function automatic bit look(const ref logic x);\n"
      "    return x;\n"
      "  endfunction\n"
      "  a1: assert property (@(posedge clk) peek(a, seen));\n"
      "  a2: assert property (@(posedge clk) look(a));\n"
      "endmodule\n",
      f);
  const char* const kReport =
      "has an output, inout or ref argument and cannot be called in a "
      "concurrent assertion";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 11, "16.6"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 12, "16.6"));
}

TEST(AssertionFunctionCalls, AFunctionWithStateOrASideEffectIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a;\n"
      "  int count;\n"
      "  function bit tally(bit x);\n"
      "    count = count + 1;\n"
      "    return x;\n"
      "  endfunction\n"
      "  function bit keep(bit x);\n"
      "    int n = 0;\n"
      "    return x;\n"
      "  endfunction\n"
      "  function automatic bit clean(bit x);\n"
      "    bit y;\n"
      "    y = !x;\n"
      "    return !y;\n"
      "  endfunction\n"
      "  a1: assert property (@(posedge clk) tally(a));\n"
      "  a2: assert property (@(posedge clk) keep(a));\n"
      "  a3: assert property (@(posedge clk) clean(a));\n"
      "endmodule\n",
      f);
  const char* const kReport =
      "keeps state or has a side effect and cannot be called in a concurrent "
      "assertion";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 17, "16.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 18, "16.6"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 19, "16.6"));
}

TEST(AssertionFunctionCalls, AnIncrementInAnAssertionExpressionIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a;\n"
      "  int n;\n"
      "  a1: assert property (@(posedge clk) n++ < 10);\n"
      "  sequence s;\n"
      "    int x;\n"
      "    @(posedge clk) (a, x = 0) ##1 (a, x++);\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  const char* const kReport =
      "an increment or decrement in a concurrent assertion expression is a "
      "side effect";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 4, "16.6"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 7, "16.6"));
}

const char kNotIntegral[] =
    "a concurrent assertion's expression shall be cast compatible with an "
    "integral type";

const char kTypes[] =
    "interface ifc; logic s; endinterface\n"
    "class L; local int x; endclass\n"
    "class P; protected int x; endclass\n"
    "class LD extends L; endclass\n"
    "class PD extends P; endclass\n"
    "class C; int x; endclass\n"
    "class CB; int y; endclass\n"
    "class CD extends CB; int z; endclass\n"
    "class R; real x; endclass\n"
    "class E; event e; endclass\n"
    "class EC; endclass\n"
    "typedef union {int i; byte b;} u_t;\n"
    "typedef enum {RED, GREEN} color_t;\n";

const char kDecls[] =
    "  logic clk = 0, a = 1;\n"
    "  event ev; virtual ifc vif;\n"
    "  L lh; P ph; LD ldh; PD pdh; C ch; CD cdh; R rh; E eh; EC eh0;\n"
    "  u_t u, u2; struct {int i; byte b;} us;\n"
    "  real ra[2]; shortreal sa[2]; realtime ta[2]; int ia[2]; event ea[2];\n"
    "  struct {real r;} rs; struct {int x;} is; struct {u_t m;} um;\n"
    "  struct {union packed {int i; bit [31:0] b;} m;} pm;\n"
    "  struct {event e;} es; struct {int q[$];} qs;\n"
    "  real rq[$]; real rd[]; real raa[int]; int iq[$]; int id[]; int "
    "iaa[int];\n"
    "  int n; bit [7:0] b8; color_t c; struct packed {bit p; bit q;} ps;\n"
    "  union packed {bit [1:0] w; bit [1:0] v;} pu; real r; shortreal sr;\n"
    "  realtime rt; string str;\n"
    "  function automatic u_t fu(); return u; endfunction\n";

std::string TypeBench(const std::string& items,
                      const std::string& outside = "") {
  return std::string(kTypes) + outside + "module top;\n" + kDecls + "  " +
         items + "\nendmodule\n";
}

std::string Replaced(std::string text, const std::string& with) {
  for (size_t at = text.find("@@"); at != std::string::npos;
       at = text.find("@@", at + with.size())) {
    text.replace(at, 2, with);
  }
  return text;
}

void ExpectTypeReported(const std::string& items, const std::string& form,
                        const std::string& outside = "") {
  const std::string kMarked = TypeBench(items, outside);
  const std::string kSrc = Replaced(kMarked, form);
  ElabFixture f;
  Elaborate(kSrc, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNotIntegral,
                            LineHolding(kMarked, "@@"), "16.6"))
      << kSrc;
}

void ExpectTypeAccepted(const std::string& items,
                        const std::string& outside = "") {
  const std::string kSrc = TypeBench(items, outside);
  ElabFixture f;
  auto* design = Elaborate(kSrc, f);
  ASSERT_NE(design, nullptr) << kSrc;
  EXPECT_FALSE(f.has_errors) << kSrc;
}

const char kWhole[] = "assert property (@(posedge clk) @@);";

void ExpectEachWholeReported(std::initializer_list<const char*> forms) {
  for (const char* form : forms) ExpectTypeReported(kWhole, form);
}

void ExpectEachWholeAccepted(std::initializer_list<const char*> forms) {
  for (const char* form : forms) ExpectTypeAccepted(Replaced(kWhole, form));
}

TEST(AssertionExpressionType, EveryIntegralOrRealOrStringWholeIsAccepted) {
  ExpectEachWholeAccepted({"n", "b8", "c", "ps", "pu", "r", "sr", "rt", "str"});
}

TEST(AssertionExpressionType, EveryBitStreamAggregateWholeIsAccepted) {
  ExpectEachWholeAccepted(
      {"ia", "is", "iq", "id", "iaa", "qs", "us", "pm", "ch", "cdh", "eh0"});
}

TEST(AssertionExpressionType, TheNearestAllowedFormsAreAccepted) {
  ExpectEachWholeAccepted({"ev.triggered", "ev == null", "u.i", "vif.s",
                           "vif != null", "lh == null", "ea[0].triggered",
                           "es.e.triggered", "a ? u.i : u2.i", "fu().i"});
  ExpectTypeAccepted("assert property (@(ev) a);");
}

TEST(AssertionExpressionType, DISABLED_AnEventOrUnpackedUnionIsReported) {
  ExpectEachWholeReported({"ev", "u"});
}

TEST(AssertionExpressionType, DISABLED_AVirtualInterfaceIsReported) {
  ExpectEachWholeReported({"vif"});
}

TEST(AssertionExpressionType,
     DISABLED_AHandleWithALocalOrProtectedMemberIsReported) {
  ExpectEachWholeReported({"lh", "ph", "ldh", "pdh"});
}

TEST(AssertionExpressionType, DISABLED_AnAggregateOfANonBitStreamIsReported) {
  ExpectEachWholeReported(
      {"ra", "sa", "ta", "ea", "rs", "um", "es", "rq", "rd", "raa"});
}

TEST(AssertionExpressionType,
     DISABLED_AHandleWithANonBitStreamMemberIsReported) {
  ExpectEachWholeReported({"rh", "eh"});
}

TEST(AssertionExpressionType, DISABLED_AnOperatorOrCallResultIsReported) {
  ExpectEachWholeReported({"a ? u : u2", "fu()"});
}

const char* const kPlaces[] = {
    "assert property (@(posedge clk) @@);",
    "assume property (@(posedge clk) @@);",
    "cover property (@(posedge clk) @@);",
    "restrict property (@(posedge clk) @@);",
    "property pp; @(posedge clk) @@; endproperty\n  assert property (pp);",
    "sequence sq; @(posedge clk) @@; endsequence\n  assert property (sq);",
    "assert property (@(posedge clk) a ##1 @@);",
    "assert property (@(posedge clk) a |-> @@);",
    "assert property (@(posedge clk) disable iff (@@) a);",
    "default disable iff (@@);\n  assert property (@(posedge clk) a);",
    "always @(posedge clk) assert property (@@);",
    "initial assert property (@(posedge clk) @@);",
    "if (1) begin : g assert property (@(posedge clk) @@); end",
};

TEST(AssertionExpressionType, EveryPlaceAcceptsAnIntegralExpression) {
  for (const char* place : kPlaces) ExpectTypeAccepted(Replaced(place, "a"));
}

TEST(AssertionExpressionType, DISABLED_EveryPlaceReportsAnExcludedType) {
  for (const char* place : kPlaces) {
    for (const char* form : {"ev", "u", "vif", "lh", "ra", "rh"}) {
      ExpectTypeReported(place, form);
    }
  }
}

std::string Unit(const char* kind) {
  return std::string(kind) + " u_unit(input logic clk);\n  u_t u;\n  " +
         "assert property (@(posedge clk) @@);\nend" + kind + "\n";
}

TEST(AssertionExpressionType, DISABLED_EveryUnitReportsAnExcludedType) {
  for (const char* kind : {"interface", "program", "checker"}) {
    ExpectTypeReported("u_unit k(clk);", "u", Unit(kind));
  }
  ExpectTypeReported("assert property (pk::pkp(u, clk));", "x",
                     "package pk;\n"
                     "  property pkp(u_t x, logic c); @(posedge c) @@; "
                     "endproperty\n"
                     "endpackage\n");
}

TEST(AssertionExpressionType, EveryUnitAcceptsAnIntegralExpression) {
  for (const char* kind : {"interface", "program", "checker"}) {
    ExpectTypeAccepted("u_unit k(clk);", Replaced(Unit(kind), "u.i"));
  }
  ExpectTypeAccepted("assert property (pk::pkp(u, clk));",
                     "package pk;\n"
                     "  property pkp(u_t x, logic c); @(posedge c) x.i; "
                     "endproperty\n"
                     "endpackage\n");
}

const char kStaticReadsAutomatic[] =
    "a static concurrent assertion shall not reference an automatic variable";

const char kLifetimes[] =
    "  task automatic ta(input int a); int x; x = a; endtask\n"
    "  task static ts(input int a); int x; x = a; endtask\n"
    "  function automatic int fa(); int v; v = 1; return v; endfunction\n"
    "  function static int fs(); int v; v = 1; return v; endfunction\n";

std::string LifetimeBench(const std::string& items,
                          const std::string& outside = "",
                          const char* lifetime = "") {
  return outside + "module " + lifetime +
         "top;\n"
         "  logic clk = 0, a = 1;\n" +
         kLifetimes +
         "  initial begin : ib automatic int y; static int z; y = 1; z = 1; "
         "end\n"
         "  initial begin : mb int w; static int s; w = 1; s = 1; end\n"
         "  " +
         items + "\nendmodule\n";
}

void ExpectAutomaticReported(const std::string& marked,
                             const std::string& form) {
  const std::string kSrc = Replaced(marked, form);
  ElabFixture f;
  Elaborate(kSrc, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kStaticReadsAutomatic,
                            LineHolding(marked, "@@"), "16.6"))
      << kSrc;
}

void ExpectLifetimeAccepted(const std::string& src) {
  ElabFixture f;
  auto* design = Elaborate(src, f);
  ASSERT_NE(design, nullptr) << src;
  EXPECT_FALSE(f.has_errors) << src;
}

const char kStaticRead[] = "assert property (@(posedge clk) @@ == 1);";

TEST(StaticAssertionAutomaticRef,
     AStaticVariableNamedHierarchicallyIsAccepted) {
  for (const char* form : {"ts.x", "ts.a", "fs.v", "ib.z"}) {
    ExpectLifetimeAccepted(LifetimeBench(Replaced(kStaticRead, form)));
  }
  ExpectLifetimeAccepted(
      LifetimeBench(Replaced(kStaticRead, "mb.s"), "", "automatic "));
}

TEST(StaticAssertionAutomaticRef,
     DISABLED_ASubroutinesOrBlocksAutomaticVariableIsReported) {
  for (const char* form : {"ta.x", "ta.a", "fa.v", "ib.y"}) {
    ExpectAutomaticReported(LifetimeBench(kStaticRead), form);
  }
}

TEST(StaticAssertionAutomaticRef,
     DISABLED_AnAutomaticModulesBlockVariableIsReported) {
  ExpectAutomaticReported(LifetimeBench(kStaticRead, "", "automatic "), "mb.w");
}

const char* const kStaticPlaces[] = {
    "assert property (@(posedge clk) @@ == 1);",
    "assume property (@(posedge clk) @@ == 1);",
    "cover property (@(posedge clk) @@ == 1);",
    "restrict property (@(posedge clk) @@ == 1);",
    ("property pp; @(posedge clk) @@ == 1; endproperty\n  assert property "
     "(pp);"),
    ("sequence sq; @(posedge clk) @@ == 1; endsequence\n  assert property "
     "(sq);"),
    "let lt = @@ == 1;\n  assert property (@(posedge clk) lt);",
    "assert property (@(posedge clk) disable iff (@@ == 1) a);",
    "default disable iff (@@ == 1);\n  assert property (@(posedge clk) a);",
    "if (1) begin : g assert property (@(posedge clk) @@ == 1); end",
};

TEST(StaticAssertionAutomaticRef, EveryStaticPlaceAcceptsAStaticVariable) {
  for (const char* place : kStaticPlaces) {
    ExpectLifetimeAccepted(LifetimeBench(Replaced(place, "fs.v")));
  }
}

TEST(StaticAssertionAutomaticRef,
     DISABLED_EveryStaticPlaceReportsAnAutomaticVariable) {
  for (const char* place : kStaticPlaces) {
    ExpectAutomaticReported(LifetimeBench(place), "fa.v");
  }
}

std::string LifetimeUnit(const char* kind) {
  return std::string(kind) + " u_unit(input logic clk);\n" + kLifetimes +
         "  assert property (@(posedge clk) @@ == 1);\nend" + kind + "\n";
}

const char kLifetimeChecker[] =
    "checker u_unit(logic clk);\n"
    "  function automatic int fa(); int v; v = 1; return v; endfunction\n"
    "  function static int fs(); int v; v = 1; return v; endfunction\n"
    "  assert property (@(posedge clk) @@ == 1);\n"
    "endchecker\n";

TEST(StaticAssertionAutomaticRef, EveryUnitAcceptsAStaticVariable) {
  for (const std::string& unit :
       {LifetimeUnit("interface"), LifetimeUnit("program"),
        std::string(kLifetimeChecker)}) {
    ExpectLifetimeAccepted(
        LifetimeBench("u_unit u(clk);", Replaced(unit, "fs.v")));
  }
}

TEST(StaticAssertionAutomaticRef,
     DISABLED_EveryUnitReportsAnAutomaticVariable) {
  for (const std::string& unit :
       {LifetimeUnit("interface"), LifetimeUnit("program"),
        std::string(kLifetimeChecker)}) {
    const std::string kMarked = LifetimeBench("u_unit u(clk);", unit);
    ExpectAutomaticReported(kMarked, "fa.v");
  }
}

}  // namespace
