#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>

#include "elaborator/let_construct.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(LetDeclElaboration, BasicLetDeclElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  let add(a, b) = a + b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LetDeclElaboration, LetDeclNoArgsElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  let val = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LetDeclElaboration, LetDeclWithDefaultsElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  let inc(x, step = 1) = x + step;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LetDeclElaboration, LetDeclUntypedArgElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  let pass(untyped a) = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LetDeclElaboration, LetDeclTypedArgElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  let mul(logic [15:0] x, logic [15:0] y) = x * y;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LetDeclElaboration, MultipleLetDeclsElaborate) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  let add(a, b) = a + b;\n"
      "  let sub(a, b) = a - b;\n"
      "  let mul(a, b) = a * b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LetDeclElaboration, LetDeclInPackageElaborates) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  let op(x, y) = x & y;\n"
             "endpackage\n"
             "module m;\n"
             "endmodule\n",
             f));
}

TEST(LetDeclElaboration, LetDeclInInterfaceElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "interface ifc;\n"
      "  let valid(req, ack) = req & ack;\n"
      "endinterface\n"
      "module m;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LetDeclElaboration, LetDeclWithComplexBodyElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  let max(a, b) = (a > b) ? a : b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LetDeclElaboration, LetDeclInBlockItemElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  initial begin\n"
      "    let local_add(a, b) = a + b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LetDeclElaboration, LetDeclWithAttributeElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  let f((* mark *) logic x) = x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LetDeclElaboration, LetDeclInProgramElaborates) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("program p;\n"
             "  let inc(x) = x + 1;\n"
             "endprogram\n"
             "module m;\n"
             "endmodule\n",
             f));
}

TEST(LetDeclElaboration, LetDeclInCheckerElaborates) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("checker chk;\n"
             "  let valid(a, b) = a | b;\n"
             "endchecker\n"
             "module m;\n"
             "endmodule\n",
             f));
}

TEST(LetDeclElaboration, LetDeclInGenerateBlockElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  generate\n"
      "    if (1) begin\n"
      "      let g(x) = x + 1;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LetDeclElaboration, LetDeclInFunctionElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  function int foo();\n"
      "    let inc(x) = x + 1;\n"
      "    return inc(5);\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LetDeclElaboration, LetDeclInTaskElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  task my_task();\n"
      "    let inc(x) = x + 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LetConstructRules, TypedFormalMustBeEventOrAllowedDataType) {
  EXPECT_TRUE(IsLetFormalTypeAllowed(LetFormalTypeKind::kUntyped));
  EXPECT_TRUE(IsLetFormalTypeAllowed(LetFormalTypeKind::kEvent));
  EXPECT_TRUE(
      IsLetFormalTypeAllowed(LetFormalTypeKind::kAssertionExpressionType));
  EXPECT_FALSE(IsLetFormalTypeAllowed(LetFormalTypeKind::kForbidden));
}

TEST(LetConstructRules, EventFormalRequiresEventExpressionActual) {
  EXPECT_TRUE(IsLetEventFormalActualLegal(true));
  EXPECT_FALSE(IsLetEventFormalActualLegal(false));
}

TEST(LetConstructRules, EventTypedFormalReferenceMustBeEventExpressionPlace) {
  EXPECT_TRUE(IsLetEventTypedFormalRefLegal(true));
  EXPECT_FALSE(IsLetEventTypedFormalRefLegal(false));
}

TEST(LetConstructRules, NonEventFormalRequiresCastCompatibleActual) {
  EXPECT_TRUE(IsLetNonEventFormalActualLegal(true));
  EXPECT_FALSE(IsLetNonEventFormalActualLegal(false));
}

TEST(LetConstructRules, SubstitutionCastsOnlyNonEventFormals) {
  EXPECT_EQ(LetTypedFormalSubstitution(true),
            LetTypedFormalSubstitutionMode::kEventExpressionSubstitution);
  EXPECT_EQ(LetTypedFormalSubstitution(false),
            LetTypedFormalSubstitutionMode::kCastBeforeSubstitution);
}

TEST(LetConstructRules, BodyMustBeDefinedBeforeUse) {
  EXPECT_TRUE(IsLetUseAfterDeclarationLegal(true));
  EXPECT_FALSE(IsLetUseAfterDeclarationLegal(false));
}

TEST(LetConstructRules, HierarchicalReferenceToLetIsIllegal) {
  EXPECT_TRUE(IsLetReferenceLegal(false));
  EXPECT_FALSE(IsLetReferenceLegal(true));
}

TEST(LetConstructRules, SampledValueClockMustBeResolvableInContext) {
  EXPECT_TRUE(
      IsLetSampledValueClockResolved(LetSampledValueClockStatus::kExplicit));
  EXPECT_TRUE(IsLetSampledValueClockResolved(
      LetSampledValueClockStatus::kInferredFromContext));
  EXPECT_FALSE(IsLetSampledValueClockResolved(
      LetSampledValueClockStatus::kRequiredButNotInferable));
}

TEST(LetDeclElaboration, LetFormalWithChandleTypeIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  let f(chandle x) = x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "let formal argument 'x' must be of type event or a type allowed in a "
      "Boolean expression",
      2, "11.12"));
}

TEST(LetDeclElaboration, LetFormalWithVoidTypeIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  let f(void x) = x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "let formal argument 'x' must be of type event or a type allowed in a "
      "Boolean expression",
      2, "11.12"));
}

TEST(LetDeclElaboration, LetFormalWithAllowedTypeElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  let f(int x) = x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LetDeclElaboration, LetFormalWithEventTypeElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  let f(event ev) = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LetDeclElaboration, LetUsedBeforeItsDeclarationIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic a = 1, b = 0;\n"
      "  initial $display(\"ran %0d\", tmp);\n"
      "  let tmp = a && b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "let 'tmp' is used before its declaration", 3,
                            "11.12"));
}

TEST(LetDeclElaboration, LetCalledBeforeItsDeclarationIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic a = 1, y, z;\n"
      "  assign y = inv(a);\n"
      "  let inv(x) = !x;\n"
      "  assign z = inv(a);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "let 'inv' is used before its declaration", 3,
                            "11.12"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

TEST(LetDeclElaboration, HierarchicalReferenceToALetIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire a = 1'b0, b = 1'b1;\n"
      "  wire [2:0] c = 3'b101;\n"
      "  wire [2:0] d;\n"
      "  wire e;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 3; i++) begin : L0\n"
      "    if (i != 1) begin : L1\n"
      "      let my_let(x) = !x || b && c[i];\n"
      "      assign d[2 - i] = my_let(a);\n"
      "    end\n"
      "  end\n"
      "  assign e = L0[0].L1.my_let(a);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a let shall not be referenced hierarchically", 13,
                            "11.12"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

TEST(LetElaboration, HierarchicalReferenceToAChildModulesLetReported) {
  ElabFixture f;
  ElaborateSrc(
      "module child;\n"
      "  let my_let(x) = !x;\n"
      "endmodule\n"
      "module top;\n"
      "  child u();\n"
      "  logic r;\n"
      "  initial r = u.my_let(1'b0);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a let shall not be referenced hierarchically", 7,
                            "11.12"));
}

TEST(LetElaboration, LetUsedBeforeDeclarationInANestedScopeReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic y, z;\n"
      "  if (1) begin : g\n"
      "    assign y = f;\n"
      "    let f = 1'b1;\n"
      "  end else begin : e\n"
      "    assign y = f2;\n"
      "    let f2 = 1'b0;\n"
      "  end\n"
      "  case (1)\n"
      "    1: begin : c\n"
      "      assign z = f3;\n"
      "      let f3 = 1'b1;\n"
      "    end\n"
      "  endcase\n"
      "  initial begin\n"
      "    static int v = h;\n"
      "    let h = 1;\n"
      "    $display(\"%0d\", h);\n"
      "  end\n"
      "  initial begin\n"
      "    typedef int t_t;\n"
      "    t_t k;\n"
      "  end\n"
      "  function automatic int fn();\n"
      "    begin\n"
      "      int w = q;\n"
      "      let q = 2;\n"
      "    end\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  for (auto [line, name] :
       {std::pair{4u, "f"}, std::pair{7u, "f2"}, std::pair{12u, "f3"},
        std::pair{17u, "h"}, std::pair{27u, "q"}}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        std::string("let '") + name + "' is used before its declaration", line,
        "11.12"));
  }
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "let 'h' is used before its declaration", 19,
                             "11.12"));
}

TEST(LetDeclElaboration, EventFormalReferencedAsAValueReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a;\n"
      "  let f(event e) = e + 1;\n"
      "  let g(event e) = $rose(a, @(e));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "event formal 'e' of a let is referenced where no "
                            "event_expression may be written",
                            3, "11.12"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "event formal 'e' of a let is referenced", 4,
                             "11.12"));
}

TEST(LetDeclElaboration, FormalTakingEventFromTheOneBeforeItReported) {
  ElabFixture f;
  ElaborateSrc(
      "int i;\n"
      "let k(event e, y) = y + 1;\n"
      "let h(event e, type(i) y) = y + 1;\n"
      "module m;\n"
      "  let f(event e, y) = y + 1;\n"
      "  let g(event e, untyped y) = y;\n"
      "endmodule\n",
      f);
  for (uint32_t line : {2u, 5u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "event formal 'y' of a let is referenced where "
                              "no event_expression may be written",
                              line, "11.12"));
  }
  for (uint32_t line : {3u, 6u}) {
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                               "event formal 'y' of a let is referenced", line,
                               "11.12"));
  }
}

TEST(LetDeclElaboration, ActualNotCastCompatibleWithTypedFormalReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C; local int v; endclass\n"
      "module m;\n"
      "  typedef struct { int a; byte b; } s_t;\n"
      "  typedef struct packed { int a; } p_t;\n"
      "  s_t s; p_t p; C h; int i; int arr [2];\n"
      "  union { int x; real y; } un;\n"
      "  union soft { int x; byte y; } su;\n"
      "  localparam int P = 1;\n"
      "  let g(int x) = x;\n"
      "  let r(real x) = x;\n"
      "  let u(x) = x;\n"
      "  let t(s_t x) = x.a;\n"
      "  let d(int x = s) = x;\n"
      "  let k(int x = 1) = x;\n"
      "  initial begin\n"
      "    $display(\"%0d\", g(s));\n"
      "    $display(\"%0d\", r(.x(arr)));\n"
      "    $display(\"%0d\", g(un));\n"
      "    $display(\"%0d\", u(s));\n"
      "    $display(\"%0d\", t(s));\n"
      "    $display(\"%0d\", g(p) + g(i) + g(P) + g(3) + g(su) + k());\n"
      "    $display(\"%0d\", g(h));\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line : {13u, 16u, 17u, 18u, 22u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "is not cast compatible with the type of formal",
                              line, "11.12"));
  }
  for (uint32_t line : {19u, 20u, 21u}) {
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                               "is not cast compatible with the type of formal",
                               line, "11.12"));
  }
}

TEST(LetDeclElaboration, LetSampledValueWithNoInferableClockReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input clock);\n"
      "  logic a, b;\n"
      "  let p1(x) = $past(x);\n"
      "  let p2 = $rose(a, @(posedge clock));\n"
      "  let p3(x) = $bits(x) + $sampled(x);\n"
      "  always_comb begin\n"
      "    a1: assert (p1(a));\n"
      "    a2: assert (p2);\n"
      "    a3: assert (p3(a));\n"
      "    a4: assert property (@(posedge clock) p1(a));\n"
      "  end\n"
      "  always @(posedge clock) begin\n"
      "    b <= p1(a);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "no clock is inferred where let 'p1' is "
                            "instantiated",
                            7, "11.12"));
  for (uint32_t line : {8u, 9u, 10u, 13u}) {
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "no clock is inferred",
                               line, "11.12"));
  }
}

TEST(LetDeclElaboration, LetSampledValueClockedByDefaultClockingAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input clock);\n"
      "  logic a;\n"
      "  default clocking cb @(posedge clock); endclocking\n"
      "  let p1(x) = $past(x);\n"
      "  always_comb a1: assert (p1(a));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), "no clock is inferred", 5, "11.12"));
}

TEST(LetDeclElaboration, ActualTypesAreJudgedByCastCompatibility) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef struct { int a; byte b; } s_t;\n"
      "  typedef struct { int a; } t_t;\n"
      "  typedef enum {E0, E1} e_t;\n"
      "  s_t s; t_t t; int arr [2], brr [2]; int i; e_t e; string str;"
      " real rv; chandle ch; class C; endclass let cl(C x) = 1;\n"
      "  let g(s_t x) = x.a;\n"
      "  let h(int x) = x;\n"
      "  let r(real x) = x; let sx(string x) = x.len();\n"
      "  initial begin\n"
      "    automatic s_t loc;\n"
      "    $display(\"%0d\", g(arr));\n"
      "    $display(\"%0d\", g(t));\n"
      "    $display(\"%0d\", h(loc));\n"
      "    $display(\"%0d\", r(i) + h(e) + h(str) + sx(i) + g(s));\n"
      "    $display(\"%0d\", g(i));\n"
      "    $display(\"%0d\", g(rv));\n"
      "    $display(\"%0d\", h(ch));\n"
      "    $display(\"%0d\", cl(i));\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line : {11u, 12u, 13u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "is not cast compatible with the type of formal",
                              line, "11.12"));
  }
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "is not cast compatible with the type of formal",
                             14, "11.12"));
  for (uint32_t line : {15u, 16u, 17u, 18u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "is not cast compatible with the type of formal",
                              line, "11.12"));
  }
}

TEST(LetDeclElaboration, ClassActualsAndFormalsAreJudgedByTheirHierarchy) {
  ElabFixture f;
  ElaborateSrc(
      "class B; protected int p; endclass\n"
      "class D extends B; endclass\n"
      "class U; endclass\n"
      "package pk; typedef int int_t; endpackage\n"
      "module m;\n"
      "  typedef B b_t;\n"
      "  B b; D d; U u; b_t tb; pk::int_t pi; int i; string str;\n"
      "  let lb(B x) = 1;\n"
      "  let ld(D x) = 1;\n"
      "  let lt(b_t x) = 1;\n"
      "  let g(int x) = x;\n"
      "  let s(string x) = x.len();\n"
      "  initial begin\n"
      "    $display(\"%0d\", lb(b) + lb(d) + ld(b) + lb(tb) + lt(b) + g(pi));\n"
      "    $display(\"%0d\", lb(u));\n"
      "    $display(\"%0d\", g(b));\n"
      "    $display(\"%0d\", s(d));\n"
      "    $display(\"%0d\", lb(i));\n"
      "    $display(\"%0d\", ld(str));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "is not cast compatible with the type of formal",
                             14, "11.12"));
  for (uint32_t line : {15u, 16u, 17u, 18u, 19u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "is not cast compatible with the type of formal",
                              line, "11.12"));
  }
}

TEST(LetDeclElaboration, ClassesNamedThroughTypedefsAndPackagesAreJudged) {
  ElabFixture f;
  ElaborateSrc(
      "class B; endclass\n"
      "package pk; typedef int int_t; endpackage\n"
      "package pc;\n"
      "  typedef int n_t;\n"
      "  class P; endclass\n"
      "  class P2 extends P; endclass\n"
      "endpackage\n"
      "module m;\n"
      "  typedef B b_t;\n"
      "  typedef b_t bb_t;\n"
      "  B b; bb_t tb; pk::int_t pi; int i; pc::P p; pc::P2 p2;\n"
      "  let lb(B x) = 1;\n"
      "  let lt(bb_t x) = 1;\n"
      "  let lp(pc::P x) = 1;\n"
      "  initial begin\n"
      "    $display(\"%0d\", lt(b) + lb(tb) + lp(p2) + lp(p));\n"
      "    $display(\"%0d\", lt(i));\n"
      "    $display(\"%0d\", lb(pi));\n"
      "    $display(\"%0d\", lp(b));\n"
      "    $display(\"%0d\", lb(p2));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "is not cast compatible with the type of formal",
                             16, "11.12"));
  for (uint32_t line : {17u, 18u, 19u, 20u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "is not cast compatible with the type of formal",
                              line, "11.12"));
  }
}

TEST(LetDeclElaboration, NestedClassesNamedThroughTheirOuterClassAreJudged) {
  ElabFixture f;
  ElaborateSrc(
      "class Base; endclass\n"
      "class Inner; endclass\n"
      "class Outer;\n"
      "  class Inner extends Base; endclass\n"
      "endclass\n"
      "module m;\n"
      "  Base b; Inner ti; Outer::Inner oi;\n"
      "  let lb(Base x) = 1;\n"
      "  let lo(Outer::Inner x) = 1;\n"
      "  initial begin\n"
      "    $display(\"%0d\", lb(oi) + lo(oi) + lo(b));\n"
      "    $display(\"%0d\", lb(ti));\n"
      "    $display(\"%0d\", lo(ti));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "is not cast compatible with the type of formal",
                             11, "11.12"));
  for (uint32_t line : {12u, 13u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "is not cast compatible with the type of formal",
                              line, "11.12"));
  }
}

TEST(LetDeclElaboration, StringActualsAndFormalsAreJudgedAsBitStreamTypes) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  typedef logic [3:0] w_t;\n"
      "  typedef struct { int a; string s; w_t w; C c;"
      " struct packed { bit b; } p; enum { E0 } e; } ok_t;\n"
      "  typedef struct { real r; } bad_t;\n"
      "  typedef union { int a; real r; } badu_t;\n"
      "  typedef struct packed { int a; } p_t;\n"
      "  ok_t ok; bad_t bad; badu_t bu; p_t pk; string str; int i; real rv;"
      " chandle ch;\n"
      "  union soft { int x; byte y; } su;\n"
      "  let s(string x) = x.len();\n"
      "  let r(real x) = x;\n"
      "  initial begin\n"
      "    $display(\"%0d\", s(str) + s(i) + s(ok) + s(pk) + s(su));\n"
      "    $display(\"%0d\", r(str));\n"
      "    $display(\"%0d\", s(rv));\n"
      "    $display(\"%0d\", s(bad));\n"
      "    $display(\"%0d\", s(bu));\n"
      "    $display(\"%0d\", s(ch));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "is not cast compatible with the type of formal",
                             13, "11.12"));
  for (uint32_t line : {14u, 15u, 16u, 17u, 18u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "is not cast compatible with the type of formal",
                              line, "11.12"));
  }
}

TEST(LetDeclElaboration, ActualForFormalWritingOnlySigningOrDimensionJudged) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef struct { int a; } s_t;\n"
      "  s_t s; int arr [2]; int i; real rv; string str;\n"
      "  let w([3:0] x) = x;\n"
      "  let g(signed x) = x;\n"
      "  let u(x) = x;\n"
      "  initial begin\n"
      "    $display(\"%0d\", w(arr));\n"
      "    $display(\"%0d\", g(arr));\n"
      "    $display(\"%0d\", w(s));\n"
      "    $display(\"%0d\", g(.x(s)));\n"
      "    $display(\"%0d\", w(i) + w(rv) + g(str) + u(arr) + u(s));\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line : {8u, 9u, 10u, 11u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "is not cast compatible with the type of formal",
                              line, "11.12"));
  }
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "is not cast compatible with the type of formal",
                             12, "11.12"));
}

TEST(LetDeclElaboration, ActualForFormalTakingTypeWrittenBeforeItJudged) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef struct { int a; byte b; } s_t;\n"
      "  typedef int arr_t [3];\n"
      "  s_t s; int arr [2]; int i; arr_t u;\n"
      "  let f(int x, y) = x + y;\n"
      "  let w([3:0] x, y) = x;\n"
      "  let g(int x, untyped y, z) = x;\n"
      "  let d(int x, y = arr) = x;\n"
      "  let p(arr_t x, y) = x[0];\n"
      "  let q(int x [3], y) = y;\n"
      "  if (1) begin : gb\n"
      "    let t(int x, type(s) y, z) = x;\n"
      "    initial $display(\"%0d\", t(1, s, s));\n"
      "  end\n"
      "  initial begin\n"
      "    $display(\"%0d\", f(1, arr));\n"
      "    $display(\"%0d\", f(.x(1), .y(s)));\n"
      "    $display(\"%0d\", w(1, s));\n"
      "    $display(\"%0d\", g(1, arr, s) + g(.x(1), .y(s), .z(arr)));\n"
      "    $display(\"%0d\", f(1, i) + p(u, u));\n"
      "    $display(\"%0d\", p(u, i));\n"
      "    $display(\"%0d\", q(u, u));\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line : {8u, 16u, 17u, 18u, 21u, 22u}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "is not cast compatible with the type of formal 'y'", line, "11.12"));
  }
  for (uint32_t line : {13u, 19u, 20u}) {
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                               "is not cast compatible with the type of formal",
                               line, "11.12"));
  }
}

TEST(LetElaboration, ABlocksOwnLetResolvesInItsStatements) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin let v = 3; $display(\"%0d\", v); end\n"
      "  initial fork let w = 5; $display(\"%0d\", w); join\n"
      "  initial $display(\"%0d\", u);\n"
      "endmodule\n",
      f);
  for (uint32_t line : {2u, 3u}) {
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                               "reference to unresolved identifier", line,
                               "23.9"));
  }
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'u'", 4,
                            "23.9"));
}

}  // namespace
