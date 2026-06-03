#include "fixture_elaborator.h"
#include "elaborator/let_construct.h"

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
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  let op(x, y) = x & y;\n"
             "endpackage\n"
             "module m;\n"
             "endmodule\n"));
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
  EXPECT_TRUE(
      ElabOk("program p;\n"
             "  let inc(x) = x + 1;\n"
             "endprogram\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(LetDeclElaboration, LetDeclInCheckerElaborates) {
  EXPECT_TRUE(
      ElabOk("checker chk;\n"
             "  let valid(a, b) = a | b;\n"
             "endchecker\n"
             "module m;\n"
             "endmodule\n"));
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
  EXPECT_TRUE(IsLetFormalTypeAllowed(LetFormalTypeKind::kTypeAllowedIn16_6));
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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

}
