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

// §11.12: a typed let formal shall be `event` or one of the types allowed in
// §16.6. `untyped` is the non-typed case and so is also accepted; `sequence`
// and `property` are not — that is what sets the let list apart from the
// sequence (§16.8.1) and property (§16.12.18) formal lists.
TEST(LetConstructRules, TypedFormalMustBeEventOrAllowedDataType) {
  EXPECT_TRUE(IsLetFormalTypeAllowed(LetFormalTypeKind::kUntyped));
  EXPECT_TRUE(IsLetFormalTypeAllowed(LetFormalTypeKind::kEvent));
  EXPECT_TRUE(IsLetFormalTypeAllowed(LetFormalTypeKind::kTypeAllowedIn166));
  EXPECT_FALSE(IsLetFormalTypeAllowed(LetFormalTypeKind::kForbidden));
}

// §11.12, rule 1: the actual for an event-typed formal shall be an
// event_expression.
TEST(LetConstructRules, EventFormalRequiresEventExpressionActual) {
  EXPECT_TRUE(IsLetEventFormalActualLegal(/*actual_is_event_expression=*/true));
  EXPECT_FALSE(
      IsLetEventFormalActualLegal(/*actual_is_event_expression=*/false));
}

// §11.12, rule 1: a reference to an event-typed formal is legal only where an
// event_expression may be written.
TEST(LetConstructRules, EventTypedFormalReferenceMustBeEventExpressionPlace) {
  EXPECT_TRUE(
      IsLetEventTypedFormalRefLegal(/*in_event_expression_position=*/true));
  EXPECT_FALSE(
      IsLetEventTypedFormalRefLegal(/*in_event_expression_position=*/false));
}

// §11.12, rule 2: a non-event typed formal requires its actual's
// self-determined result type to be cast compatible (§6.22.4) with the formal
// type.
TEST(LetConstructRules, NonEventFormalRequiresCastCompatibleActual) {
  EXPECT_TRUE(IsLetNonEventFormalActualLegal(
      /*self_determined_type_cast_compatible=*/true));
  EXPECT_FALSE(IsLetNonEventFormalActualLegal(
      /*self_determined_type_cast_compatible=*/false));
}

// §11.12: an event formal is substituted as an event_expression, while a
// non-event typed formal's actual is cast to the formal type before being
// substituted in the rewriting algorithm (§F.4).
TEST(LetConstructRules, SubstitutionCastsOnlyNonEventFormals) {
  EXPECT_EQ(LetTypedFormalSubstitution(/*formal_is_event=*/true),
            LetTypedFormalSubstitutionMode::kEventExpressionSubstitution);
  EXPECT_EQ(LetTypedFormalSubstitution(/*formal_is_event=*/false),
            LetTypedFormalSubstitutionMode::kCastBeforeSubstitution);
}

// §11.12: in the declaring scope, the let body shall be defined before it is
// used.
TEST(LetConstructRules, BodyMustBeDefinedBeforeUse) {
  EXPECT_TRUE(IsLetUseAfterDeclarationLegal(/*declared_before_use=*/true));
  EXPECT_FALSE(IsLetUseAfterDeclarationLegal(/*declared_before_use=*/false));
}

// §11.12: no hierarchical references to let declarations are allowed.
TEST(LetConstructRules, HierarchicalReferenceToLetIsIllegal) {
  EXPECT_TRUE(IsLetReferenceLegal(/*is_hierarchical_reference=*/false));
  EXPECT_FALSE(IsLetReferenceLegal(/*is_hierarchical_reference=*/true));
}

// §11.12: a sampled value call in a let body inherits the instantiation
// context's clock; it is an error if a clock is required but cannot be
// inferred there.
TEST(LetConstructRules, SampledValueClockMustBeResolvableInContext) {
  EXPECT_TRUE(
      IsLetSampledValueClockResolved(LetSampledValueClockStatus::kExplicit));
  EXPECT_TRUE(IsLetSampledValueClockResolved(
      LetSampledValueClockStatus::kInferredFromContext));
  EXPECT_FALSE(IsLetSampledValueClockResolved(
      LetSampledValueClockStatus::kRequiredButNotInferable));
}

// §11.12: the elaborator applies the typed-formal rule on the real path. A
// chandle is not a type allowed in a Boolean expression, so a chandle-typed
// formal is rejected during elaboration.
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

// §11.12: a void-typed formal is likewise outside the allowed type list and is
// rejected.
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

// §11.12: an integral typed formal is a type allowed in a Boolean expression,
// so the same validation accepts it without error.
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

// §11.12: the type rule's first accepting arm is `event` itself — the text
// permits a typed formal to be `event` or one of the §16.6 types. The
// classifier and reject tests above cover the §16.6 arm (int) and the rejected
// types (chandle, void); this drives an `event`-typed formal from real source
// through the same elaborator type check to observe the `event` arm being
// accepted. The body does not reference the formal, so this isolates the
// type-acceptance decision from any event-in-Boolean-context question.
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

// §11.12 has a let declared before it is used, so a reference to `tmp` in a
// procedure written above `let tmp = a && b;` is illegal. It elaborated clean
// and read 0.
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

// The same of a let with formals called before its declaration, from a
// continuous assignment; the call after the declaration is the legal one.
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

// §11.12's example d: a let may be referred to only within the scope that
// declares it and the scopes nested in it, and the reference to my_let
// through the generate block's hierarchical name is the example's illegal
// one. It elaborated clean.
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

// §11.12 bars every hierarchical reference to a let, and a path through an
// instance to the let its module declares is one.
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

// §11.12 asks a let be declared before its use in the scope declaring it, and
// a generate block and a begin-end block are such scopes. A let used where an
// earlier statement of the block declared it, and a block declaring a type and
// no let, draw nothing.
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
      "    $display(\"%0d\", h);\n"
      "    let h = 1;\n"
      "    $display(\"%0d\", h);\n"
      "  end\n"
      "  initial begin\n"
      "    typedef int t_t;\n"
      "    t_t k;\n"
      "  end\n"
      "  function automatic int fn();\n"
      "    begin\n"
      "      fn = q;\n"
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

// §11.12, rule 1: a reference to an event formal stands where an
// event_expression may be written, which an operand of `+` is not; the
// clocking event of a sampled value call is such a place.
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

// §11.12, rule 2: an integral or real formal takes no actual of an unpacked
// array, structure or union type, whether a call binds it by position or by
// name or the declaration gives it as the default. An untyped formal, a formal
// of the structure's own type, and actuals of integral, packed or class types
// are left alone.
TEST(LetDeclElaboration, ActualNotCastCompatibleWithTypedFormalReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  typedef struct { int a; } s_t;\n"
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
  for (uint32_t line : {13u, 16u, 17u, 18u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "is not cast compatible with the type of formal",
                              line, "11.12"));
  }
  for (uint32_t line : {19u, 20u, 21u, 22u}) {
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                               "is not cast compatible with the type of formal",
                               line, "11.12"));
  }
}

// §11.12 clocks a sampled value call in a let body as if written where the let
// is instantiated, and its example (f) has an always_comb give `$past` no
// clock. A let whose call names its clock, one with no sampled value call, a
// procedure clocked by an edge and a concurrent assertion each give one.
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

// A module's default clocking clocks the call where the procedure gives none.
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

// §11.12, rule 2, by cast compatibility (§6.22.4): an unpacked array is no
// actual for a structure formal, a structure of another typedef none for
// either's formal, and a structure a block declares none for an int formal;
// an int for a real one, an enum for an int one and a structure for its own
// type's are.
TEST(LetDeclElaboration, ActualTypesAreJudgedByCastCompatibility) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef struct { int a; } s_t;\n"
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
  // An int or a real for a structure formal, and a chandle for an int one, are
  // no more cast compatible; a formal of a class type is not judged here.
  for (uint32_t line : {15u, 16u, 17u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "is not cast compatible with the type of formal",
                              line, "11.12"));
  }
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "is not cast compatible with the type of formal",
                             18, "11.12"));
}

}  // namespace
