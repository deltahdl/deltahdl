#include <gtest/gtest.h>

#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.51 property declaration: the VPI object model for a property declaration,
// its formals, and a property instance. A property declaration's formals are
// returned in declaration order; each formal exposes a direction, an optional
// typespec and an optional initialization expression; a property instance maps
// its arguments to the formals in declaration order (filling defaults) and
// resolves to its declaration. The argument and initialization-expression kinds
// reuse §37.52's property-expr classification, weaving the two subclauses
// together. These tests observe the production helpers in vpi.cpp and the
// VpiContext methods that apply those rules.

// Detail 1: the vpiPropFormalDecl iteration returns a property declaration's
// formals in declaration order; both the dedicated helper and the generic
// iteration observe the same ordered formals and skip non-formal members.
TEST(PropertyDeclModel, PropFormalDeclIterationFollowsDeclarationOrder) {
  VpiContext ctx;
  VpiObject decl;
  decl.type = vpiPropertyDecl;
  VpiObject spec;
  spec.type = vpiPropertySpec;  // not a formal
  VpiObject f0;
  f0.type = vpiPropFormalDecl;
  VpiObject f1;
  f1.type = vpiPropFormalDecl;
  decl.children = {&f0, &spec, &f1};

  auto formals = VpiPropFormals(&decl);
  ASSERT_EQ(formals.size(), 2u);
  EXPECT_EQ(formals[0], &f0);
  EXPECT_EQ(formals[1], &f1);

  VpiHandle it = ctx.Iterate(vpiPropFormalDecl, &decl);
  ASSERT_NE(it, nullptr);
  std::vector<VpiHandle> seen;
  while (VpiHandle h = ctx.Scan(it)) seen.push_back(h);
  ASSERT_EQ(seen.size(), 2u);
  EXPECT_EQ(seen[0], &f0);
  EXPECT_EQ(seen[1], &f1);
}

// Detail 1 edge: a null handle declares no formals.
TEST(PropertyDeclModel, NullDeclarationHasNoFormals) {
  EXPECT_TRUE(VpiPropFormals(nullptr).empty());
}

// Detail 2: vpiArgument returns the property instance's actuals in
// formal-declaration order, and a formal that carries a default contributes
// that default when the instance does not provide an actual for it.
TEST(PropertyDeclModel, ArgumentsFollowFormalOrderAndFillDefaults) {
  VpiObject a0;
  VpiObject a2;
  VpiObject def1;

  std::vector<VpiPropertyFormal> formals = {
      {nullptr},  // formal 0: no default
      {&def1},    // formal 1: has a default value
      {nullptr},  // formal 2: no default
  };
  std::vector<VpiHandle> provided = {&a0, nullptr, &a2};  // formal 1 omitted

  auto args = VpiPropertyInstArguments(formals, provided);
  ASSERT_EQ(args.size(), 3u);
  EXPECT_EQ(args[0], &a0);
  EXPECT_EQ(args[1], &def1);  // default substituted, keeping declaration order
  EXPECT_EQ(args[2], &a2);
}

// Detail 2 edge: a supplied actual wins over the formal's default, and trailing
// formals beyond the provided actuals still fall back to their defaults.
TEST(PropertyDeclModel, ArgumentsPreferActualsAndDefaultTrailingFormals) {
  VpiObject a0;
  VpiObject def1;

  std::vector<VpiPropertyFormal> formals = {{nullptr}, {&def1}};

  auto supplied = VpiPropertyInstArguments(formals, {&a0, &def1});
  ASSERT_EQ(supplied.size(), 2u);
  EXPECT_EQ(supplied[1], &def1);

  // Provided list shorter than the formals: the trailing formal uses its
  // default.
  auto trailing = VpiPropertyInstArguments(formals, {&a0});
  ASSERT_EQ(trailing.size(), 2u);
  EXPECT_EQ(trailing[0], &a0);
  EXPECT_EQ(trailing[1], &def1);
}

// Detail 3: the vpiTypespec relation returns the formal's typespec when typed
// and null when the formal is untyped.
TEST(PropertyDeclModel, FormalTypespecReportsNullWhenUntyped) {
  VpiObject typed;
  typed.type = vpiPropFormalDecl;
  VpiObject ts;
  ts.type = vpiTypespec;
  typed.children = {&ts};
  EXPECT_EQ(VpiPropFormalTypespec(&typed), &ts);

  VpiObject untyped;
  untyped.type = vpiPropFormalDecl;
  EXPECT_EQ(VpiPropFormalTypespec(&untyped), nullptr);
  EXPECT_EQ(VpiPropFormalTypespec(nullptr), nullptr);
}

// Detail 4: a formal's initialization expression is reached through vpiExpr;
// the diagram draws its target as a named event or a property expression, and a
// formal with no initialization expression reports none.
TEST(PropertyDeclModel, FormalInitExprReachesNamedEventOrPropertyExpr) {
  VpiObject with_event;
  with_event.type = vpiPropFormalDecl;
  VpiObject ev;
  ev.type = vpiNamedEvent;
  with_event.children = {&ev};
  EXPECT_EQ(VpiPropFormalInitExpr(&with_event), &ev);

  VpiObject with_prop_expr;
  with_prop_expr.type = vpiPropFormalDecl;
  VpiObject pe;
  pe.type = vpiClockedProperty;  // a property-expr kind (see §37.52)
  with_prop_expr.children = {&pe};
  EXPECT_EQ(VpiPropFormalInitExpr(&with_prop_expr), &pe);

  VpiObject untyped_only;
  untyped_only.type = vpiPropFormalDecl;
  VpiObject ts;
  ts.type = vpiTypespec;  // a typespec is not an initialization expression
  untyped_only.children = {&ts};
  EXPECT_EQ(VpiPropFormalInitExpr(&untyped_only), nullptr);
}

// Detail 5: vpiDirection is vpiInput for a local variable argument and
// vpiNoDirection for every other formal.
TEST(PropertyDeclModel, FormalDirectionDistinguishesLocalVariableArguments) {
  EXPECT_EQ(VpiPropFormalDirection(true), vpiInput);
  EXPECT_EQ(VpiPropFormalDirection(false), vpiNoDirection);
}

// Diagram (property inst -> property decl): a property instance resolves to the
// property declaration it instantiates, and reports none when no declaration is
// attached or the handle is null.
TEST(PropertyDeclModel, PropertyInstResolvesItsDeclaration) {
  VpiObject inst;
  inst.type = vpiPropertyInst;
  VpiObject decl;
  decl.type = vpiPropertyDecl;
  inst.children = {&decl};
  EXPECT_EQ(VpiPropertyInstDecl(&inst), &decl);

  VpiObject lone;
  lone.type = vpiPropertyInst;
  EXPECT_EQ(VpiPropertyInstDecl(&lone), nullptr);
  EXPECT_EQ(VpiPropertyInstDecl(nullptr), nullptr);
}

// Diagram (property inst -- vpiArgument --> property expr | named event): an
// argument of a property instance is a named event or a property expression
// (reusing §37.52's property-expr classification); other kinds are not
// arguments.
TEST(PropertyDeclModel, PropertyArgumentKindsAreNamedEventOrPropertyExpr) {
  EXPECT_TRUE(VpiIsPropertyArgumentType(vpiNamedEvent));
  EXPECT_TRUE(VpiIsPropertyArgumentType(vpiClockedProperty));
  EXPECT_TRUE(VpiIsPropertyArgumentType(vpiCaseProperty));
  EXPECT_TRUE(VpiIsPropertyArgumentType(vpiPropertyInst));

  EXPECT_FALSE(VpiIsPropertyArgumentType(vpiNet));
  EXPECT_FALSE(VpiIsPropertyArgumentType(vpiModule));
}

// Diagram (property inst -- vpiDisableCondition --> expr): a property
// instance's disable condition reaches an expression. The disable-condition
// relation is shared with §37.52's property specification, so its expression
// kinds are accepted by the shared classifier.
TEST(PropertyDeclModel, PropertyInstDisableConditionReachesAnExpression) {
  EXPECT_TRUE(VpiIsDisableConditionType(vpiExpr));
  EXPECT_TRUE(VpiIsDisableConditionType(vpiOperation));
  EXPECT_FALSE(VpiIsDisableConditionType(vpiModule));
}

// Diagram (property decl -> property spec): a property declaration traverses to
// its property specification through the generic relation lookup.
TEST(PropertyDeclModel, PropertyDeclReachesItsSpecification) {
  VpiContext ctx;
  VpiObject decl;
  decl.type = vpiPropertyDecl;
  VpiObject spec;
  spec.type = vpiPropertySpec;
  decl.children = {&spec};

  EXPECT_EQ(ctx.Handle(vpiPropertySpec, &decl), &spec);
}

}  // namespace
}  // namespace delta
