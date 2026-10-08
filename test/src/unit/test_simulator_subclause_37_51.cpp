#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

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
  pe.type = vpiClockedProp;  // a property-expr kind (see §37.52)
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
  inst.property_decl = &decl;
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
  EXPECT_TRUE(VpiIsPropertyArgumentType(vpiClockedProp));
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

// Diagram (property decl -> name: str vpiName, str vpiFullName; prop formal
// decl
// -> name: str vpiName): a property declaration reports both a simple name and
// a full name through vpi_get_str(), and a property formal reports its simple
// name. The full-name query falls back to the simple name when none is stored.
TEST(PropertyDeclModel, PropertyDeclAndFormalReportTheirNames) {
  VpiContext ctx;
  VpiObject decl;
  decl.type = vpiPropertyDecl;
  decl.name = "chk";
  decl.full_name = "top.chk";
  EXPECT_STREQ(ctx.GetStr(vpiName, &decl), "chk");
  EXPECT_STREQ(ctx.GetStr(vpiFullName, &decl), "top.chk");

  VpiObject formal;
  formal.type = vpiPropFormalDecl;
  formal.name = "a";
  EXPECT_STREQ(ctx.GetStr(vpiName, &formal), "a");
  // No full name stored on the formal -> the full-name query falls back to the
  // simple name.
  EXPECT_STREQ(ctx.GetStr(vpiFullName, &formal), "a");
}

class PropertyDeclsOfARun : public VpiDesignRun {
 protected:
  // The name of what `relation` reaches from `ref`, empty for nothing.
  static std::string NameReached(int relation, vpiHandle ref) {
    vpiHandle reached = ref == nullptr ? nullptr : vpi_handle(relation, ref);
    return reached == nullptr ? "" : vpi_get_str(vpiName, reached);
  }

  // The names of the objects of `relation` `ref` reaches, in the order
  // reached.
  static std::vector<std::string> NamesOf(int relation, vpiHandle ref) {
    std::vector<std::string> names;
    vpiHandle it = vpi_iterate(relation, ref);
    if (it == nullptr) return names;
    for (vpiHandle h = vpi_scan(it); h != nullptr; h = vpi_scan(it)) {
      names.emplace_back(vpi_get_str(vpiName, h));
    }
    return names;
  }
};

// A property a module declares is a property decl of its instance, named in
// it, reaching its formals in the order declared (detail 1), each of no
// direction (detail 5) and a default value through vpiExpr (detail 4), and its
// property spec (#5086).
TEST_F(PropertyDeclsOfARun, AnInstanceReachesThePropertyItDeclares) {
  Run("module top; logic clk, rst, a, b;\n"
      "  property p(x, y = b);\n"
      "    @(posedge clk) disable iff (rst) a;\n"
      "  endproperty\n"
      "endmodule\n");
  vpiHandle decl = Named(vpiPropertyDecl, By("top"), "p");
  ASSERT_NE(decl, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, decl), "top.p");
  EXPECT_EQ(NamesOf(vpiPropFormalDecl, decl),
            (std::vector<std::string>{"x", "y"}));
  vpiHandle y = Named(vpiPropFormalDecl, decl, "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(vpi_get(vpiDirection, y), vpiNoDirection);
  EXPECT_EQ(NameReached(vpiExpr, y), "b");
  EXPECT_EQ(NameReached(vpiExpr, Named(vpiPropFormalDecl, decl, "x")), "");
  vpiHandle spec = vpi_handle(vpiPropertySpec, decl);
  ASSERT_NE(spec, nullptr);
  EXPECT_NE(vpi_handle(vpiClockingEvent, spec), nullptr);
  EXPECT_EQ(NameReached(vpiDisableCondition, spec), "rst");
  EXPECT_EQ(NameReached(vpiPropertyExpr, spec), "a");
}

// A property a generate block declares is one of that block's instance
// (§37.12, §27.4) (#5086).
TEST_F(PropertyDeclsOfARun, AGenerateBlockReachesThePropertyItDeclares) {
  Run("module top; logic clk, a;\n"
      "  for (genvar i = 0; i < 1; i++) begin : g\n"
      "    property q; @(posedge clk) a; endproperty\n"
      "  end\n"
      "endmodule\n");
  vpiHandle decl = Named(vpiPropertyDecl, By("top.g[0]"), "q");
  ASSERT_NE(decl, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, decl), "top.g[0].q");
  EXPECT_EQ(Named(vpiPropertyDecl, By("top"), "q"), nullptr);
}

// An assertion instantiating a declared property reaches a property inst
// through vpiProperty, which reaches the declaration and its arguments in the
// order of the formals, a default standing for one not given (detail 2)
// (#5086).
TEST_F(PropertyDeclsOfARun, AnAssertionReachesThePropertyInstItWrites) {
  Run("module top; logic clk, a, b;\n"
      "  property p(x, y = b); @(posedge clk) x; endproperty\n"
      "  a1: assert property (p(a));\n"
      "endmodule\n");
  vpiHandle a1 = Named(vpiAssertion, By("top"), "a1");
  ASSERT_NE(a1, nullptr);
  vpiHandle inst = vpi_handle(vpiProperty, a1);
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(vpi_get(vpiType, inst), vpiPropertyInst);
  vpiHandle decl = vpi_handle(vpiPropertyDecl, inst);
  ASSERT_NE(decl, nullptr);
  EXPECT_TRUE(
      vpi_compare_objects(decl, Named(vpiPropertyDecl, By("top"), "p")));
  EXPECT_EQ(NamesOf(vpiArgument, inst), (std::vector<std::string>{"a", "b"}));
}

// One embedded in a procedure reaches its property inst the same way (#5086).
TEST_F(PropertyDeclsOfARun, AProceduralAssertionReachesItsPropertyInst) {
  Run("module top; logic clk, a;\n"
      "  property p(x); x; endproperty\n"
      "  always @(posedge clk) p1: assert property (p(a));\n"
      "endmodule\n");
  vpiHandle p1 = Named(vpiAssertion, By("top"), "p1");
  ASSERT_NE(p1, nullptr);
  vpiHandle inst = vpi_handle(vpiProperty, p1);
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(vpi_get(vpiType, inst), vpiPropertyInst);
  EXPECT_EQ(NameReached(vpiPropertyDecl, inst), "p");
  EXPECT_EQ(NamesOf(vpiArgument, inst), (std::vector<std::string>{"a"}));
}

// A formal declared with a type reaches a typespec of that type, and an
// untyped one none (detail 3) (#5091).
TEST_F(PropertyDeclsOfARun, ATypedFormalReachesItsTypespec) {
  Run("module top; logic clk;\n"
      "  property p(bit x, untyped y, event e, sequence s);\n"
      "    @(posedge clk) x;\n"
      "  endproperty\n"
      "endmodule\n");
  vpiHandle decl = Named(vpiPropertyDecl, By("top"), "p");
  ASSERT_NE(decl, nullptr);
  const auto kTypespecOf = [decl](const char* formal) {
    vpiHandle ts =
        vpi_handle(vpiTypespec, Named(vpiPropFormalDecl, decl, formal));
    return ts == nullptr ? 0 : vpi_get(vpiType, ts);
  };
  EXPECT_EQ(kTypespecOf("x"), vpiBitTypespec);
  EXPECT_EQ(kTypespecOf("y"), 0);
  EXPECT_EQ(kTypespecOf("e"), vpiEventTypespec);
  EXPECT_EQ(kTypespecOf("s"), vpiSequenceTypespec);
}

// A property reaches the local variables it declares (§16.10), each of the
// kind its type is (#5092).
TEST_F(PropertyDeclsOfARun, APropertyReachesItsLocalVariables) {
  Run("module top; logic clk, a;\n"
      "  property p;\n"
      "    int n; bit f;\n"
      "    @(posedge clk) a;\n"
      "  endproperty\n"
      "endmodule\n");
  vpiHandle decl = Named(vpiPropertyDecl, By("top"), "p");
  ASSERT_NE(decl, nullptr);
  EXPECT_EQ(NamesOf(vpiVariables, decl), (std::vector<std::string>{"n", "f"}));
  EXPECT_EQ(KindsOf(vpiVariables, decl),
            (std::vector<int>{vpiIntVar, vpiBitVar}));
  vpiHandle n = Named(vpiVariables, decl, "n");
  ASSERT_NE(n, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, n), "top.p.n");
}

// A property a clocking block declares is a property decl of that block
// (§37.12, §14.3), and an assertion naming it through the block, `cb.p`
// (§16.16 (b)), reaches it from its property inst (#5090).
TEST_F(PropertyDeclsOfARun, AClockingBlockReachesThePropertyItDeclares) {
  Run("module top; logic clk, a;\n"
      "  clocking cb @(posedge clk);\n"
      "    property p; a; endproperty\n"
      "  endclocking\n"
      "  a1: assert property (cb.p);\n"
      "endmodule\n");
  vpiHandle cb = Named(vpiClockingBlock, By("top"), "cb");
  ASSERT_NE(cb, nullptr);
  vpiHandle decl = Named(vpiPropertyDecl, cb, "p");
  ASSERT_NE(decl, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, decl), "top.cb.p");
  EXPECT_EQ(Named(vpiPropertyDecl, By("top"), "p"), nullptr);
  vpiHandle a1 = Named(vpiAssertion, By("top"), "a1");
  ASSERT_NE(a1, nullptr);
  vpiHandle inst = vpi_handle(vpiProperty, a1);
  ASSERT_NE(inst, nullptr);
  EXPECT_TRUE(vpi_compare_objects(vpi_handle(vpiPropertyDecl, inst), decl));
}

// A formal of a packed type reaches a typespec of its keyword with the range
// it was written with, and one of a user-defined type the typespec of the
// typedef naming it, the module's or the compilation unit's (detail 3,
// §37.25) (#5093).
TEST_F(PropertyDeclsOfARun, AFormalOfAWrittenTypeReachesItsTypespec) {
  Run("typedef logic [7:0] byte_t;\n"
      "module top; logic clk;\n"
      "  typedef struct packed { logic a, b; } pair_t;\n"
      "  property p(bit [3:0] v, pair_t s, byte_t w);\n"
      "    @(posedge clk) v[0];\n"
      "  endproperty\n"
      "endmodule\n");
  vpiHandle decl = Named(vpiPropertyDecl, By("top"), "p");
  ASSERT_NE(decl, nullptr);
  vpiHandle v = vpi_handle(vpiTypespec, Named(vpiPropFormalDecl, decl, "v"));
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(vpi_get(vpiType, v), vpiBitTypespec);
  vpiHandle ranges = vpi_iterate(vpiRange, v);
  ASSERT_NE(ranges, nullptr);
  vpiHandle range = vpi_scan(ranges);
  ASSERT_NE(range, nullptr);
  EXPECT_EQ(vpi_get(vpiSize, range), 4);
  vpiHandle s = vpi_handle(vpiTypespec, Named(vpiPropFormalDecl, decl, "s"));
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(vpi_get(vpiType, s), vpiStructTypespec);
  EXPECT_STREQ(vpi_get_str(vpiName, s), "pair_t");
  vpiHandle w = vpi_handle(vpiTypespec, Named(vpiPropFormalDecl, decl, "w"));
  ASSERT_NE(w, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, w), "byte_t");
}

// §37.51 details 3 and 4: a formal's typespec is its typespec child, found
// past a child of another kind, and a null formal has no initialization
// expression.
TEST(PropertyFormal, TypespecFoundPastOtherChildrenAndNullHasNoInit) {
  VpiObject attribute;
  attribute.type = vpiAttribute;
  VpiObject typespec;
  typespec.type = vpiTypespec;
  VpiObject formal;
  formal.type = vpiPropFormalDecl;
  formal.children = {&attribute, &typespec};
  EXPECT_EQ(VpiPropFormalTypespec(&formal), &typespec);
  EXPECT_EQ(VpiPropFormalInitExpr(nullptr), nullptr);
}

// §37.51 (figure): a property inst reaches its disable condition, and asked for
// a relation it does not draw it resolves nothing here.
TEST(PropertyDeclModel, AnInstReachesItsDisableConditionAndNoOtherTag) {
  VpiObject condition;
  condition.type = vpiOperation;
  VpiObject inst;
  inst.type = vpiPropertyInst;
  inst.disable_condition = &condition;
  VpiHandle out = nullptr;
  EXPECT_TRUE(
      TryResolveProcessAndStmtRelation(vpiDisableCondition, &inst, out));
  EXPECT_EQ(out, &condition);
  out = nullptr;
  EXPECT_FALSE(TryResolveProcessAndStmtRelation(vpiTypespec, &inst, out));
  EXPECT_EQ(out, nullptr);
}
}  // namespace
}  // namespace delta
