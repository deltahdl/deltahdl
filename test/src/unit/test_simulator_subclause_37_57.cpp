#include <gtest/gtest.h>

#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.57 Let: the VPI object model for a let construct. The diagram pairs a let
// expression (its vpiArgument iteration of actual arguments) with the let
// declaration it instantiates (reached by the tagless down arrow), where the
// declaration carries its vpiName, its body expression, and its seq formal
// decls. The one normative rule, detail 1, governs the vpiArgument iteration:
// the arguments come back in the order the formals are declared, and a formal's
// default value stands in for an argument the instantiation omits. These tests
// observe the production helper VpiLetExprArguments that applies that rule. The
// remaining diagram edges (let expr -> let decl, the vpiName property, the body
// expr, and the seq formal decls) are tagless traversals/properties carried by
// the generic VPI machinery (vpi_handle / vpi_get_str of §38.11), not by any
// rule §37.57 itself states.

// §37.57 detail 1: the vpiArgument iteration returns the arguments in
// formal-declaration order, substituting a formal's default value for an
// argument the instantiation omits. Here the middle formal is omitted but
// carries a default, so its default appears in that position while the supplied
// actuals keep their places - each argument lines up with its formal.
TEST(LetExprModel, ArgumentsFollowFormalOrderAndFillDefaults) {
  VpiObject a0;
  VpiObject a2;
  VpiObject def1;

  std::vector<VpiLetFormal> formals = {
      {nullptr},  // formal 0: no default
      {&def1},    // formal 1: has a default value
      {nullptr},  // formal 2: no default
  };
  std::vector<VpiHandle> provided = {&a0, nullptr, &a2};  // formal 1 omitted

  auto args = VpiLetExprArguments(formals, provided);
  ASSERT_EQ(args.size(), 3u);
  EXPECT_EQ(args[0], &a0);
  EXPECT_EQ(args[1], &def1);  // default substituted, declaration order kept
  EXPECT_EQ(args[2], &a2);
}

// §37.57 detail 1 (the "should the instantiation not provide a value" clause
// when there is no default): an omitted argument whose formal has no default
// value yields a null argument in that position, so later arguments still align
// with their own formals rather than shifting left.
TEST(LetExprModel, OmittedArgumentWithoutDefaultIsNull) {
  VpiObject a2;

  std::vector<VpiLetFormal> formals = {
      {nullptr},  // formal 0: no default
      {nullptr},  // formal 1: no default
  };
  std::vector<VpiHandle> provided = {nullptr, &a2};  // formal 0 omitted

  auto args = VpiLetExprArguments(formals, provided);
  ASSERT_EQ(args.size(), 2u);
  EXPECT_EQ(args[0], nullptr);  // no actual and no default
  EXPECT_EQ(args[1], &a2);      // position preserved
}

// §37.57 detail 1: the result always has one argument per formal even when the
// instantiation supplies fewer actuals than there are formals; the trailing
// formals fall back to their default values.
TEST(LetExprModel, FewerProvidedThanFormalsUsesDefaults) {
  VpiObject a0;
  VpiObject def1;

  std::vector<VpiLetFormal> formals = {
      {nullptr},  // formal 0: no default
      {&def1},    // formal 1: has a default value
  };
  std::vector<VpiHandle> provided = {&a0};  // only the first actual given

  auto args = VpiLetExprArguments(formals, provided);
  ASSERT_EQ(args.size(), 2u);
  EXPECT_EQ(args[0], &a0);
  EXPECT_EQ(args[1], &def1);  // trailing formal filled from its default
}

// §37.57 detail 1 (edge): a let with no formals has no arguments, whatever the
// instantiation happens to pass.
TEST(LetExprModel, NoFormalsYieldsNoArguments) {
  VpiObject stray;
  std::vector<VpiLetFormal> formals;
  std::vector<VpiHandle> provided = {&stray};

  EXPECT_TRUE(VpiLetExprArguments(formals, provided).empty());
}

// -----------------------------------------------------------------------------
// §37.57's vpiArgument edge, walked through the routine the diagram names for
// it. The cases above hand the rule its formals and actuals directly, which
// says what the rule does with them; nothing said whether the iteration a PLI
// application performs applies the rule at all. It did not: vpiArgument is a
// relation tag no object carries as its type, so the generic child walk the
// request fell through to reached none of the arguments, and the rule was
// stated by a helper the simulator never called.
// -----------------------------------------------------------------------------

// The fixture installs a context so the public vpi_iterate/vpi_scan entry
// points run their real dispatch over the test objects.
class LetExprIteration : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  std::vector<vpiHandle> ScanAll(vpiHandle it) {
    std::vector<vpiHandle> seen;
    if (it == nullptr) return seen;
    while (vpiHandle h = vpi_scan(it)) seen.push_back(h);
    return seen;
  }

  VpiContext ctx_;
};

// §37.57 (figure) + detail 1: the vpiArgument iteration of a let expression
// hands back its arguments, in the order the let's formals are declared.
TEST_F(LetExprIteration, TheArgumentIterationReachesTheActualsInFormalOrder) {
  VpiObject formal0;
  formal0.type = vpiSeqFormalDecl;
  VpiObject formal1;
  formal1.type = vpiSeqFormalDecl;

  VpiObject decl;
  decl.type = vpiLetDecl;
  decl.children = {&formal0, &formal1};

  VpiObject a0;
  a0.type = vpiConstant;
  VpiObject a1;
  a1.type = vpiRefObj;

  VpiObject let_expr;
  let_expr.type = vpiLetExpr;
  let_expr.children = {&decl, &a0, &a1};

  std::vector<vpiHandle> args = ScanAll(vpi_iterate(vpiArgument, &let_expr));
  ASSERT_EQ(args.size(), 2u);
  EXPECT_EQ(args[0], &a0);
  EXPECT_EQ(args[1], &a1);
}

// §37.57 detail 1: "If a formal has a default value, that value shall appear as
// the argument should the instantiation not provide a value for that argument."
// The instantiation leaves the first port empty - written the way §37.42
// detail 8 writes an omitted argument - so the formal's default stands in its
// place and the actual it did write keeps the second position.
TEST_F(LetExprIteration, AnOmittedArgumentComesBackAsItsFormalsDefault) {
  VpiObject default0;
  default0.type = vpiConstant;
  VpiObject formal0;
  formal0.type = vpiSeqFormalDecl;
  formal0.children = {&default0};
  VpiObject formal1;
  formal1.type = vpiSeqFormalDecl;

  VpiObject decl;
  decl.type = vpiLetDecl;
  decl.children = {&formal0, &formal1};

  VpiObject omitted;
  VpiMakeEmptyArgument(&omitted);
  VpiObject a1;
  a1.type = vpiRefObj;

  VpiObject let_expr;
  let_expr.type = vpiLetExpr;
  let_expr.children = {&decl, &omitted, &a1};

  std::vector<vpiHandle> args = ScanAll(vpi_iterate(vpiArgument, &let_expr));
  ASSERT_EQ(args.size(), 2u);
  EXPECT_EQ(args[0], &default0);
  EXPECT_EQ(args[1], &a1);
}

// §37.57 detail 1: the correspondence is with the formals, so an instantiation
// that writes fewer actuals than there are formals still reaches one argument
// per formal, the trailing ones coming from their defaults.
TEST_F(LetExprIteration, ATrailingFormalIsFilledFromItsDefault) {
  VpiObject default1;
  default1.type = vpiConstant;
  VpiObject formal0;
  formal0.type = vpiSeqFormalDecl;
  VpiObject formal1;
  formal1.type = vpiSeqFormalDecl;
  formal1.children = {&default1};

  VpiObject decl;
  decl.type = vpiLetDecl;
  decl.children = {&formal0, &formal1};

  VpiObject a0;
  a0.type = vpiRefObj;

  VpiObject let_expr;
  let_expr.type = vpiLetExpr;
  let_expr.children = {&decl, &a0};

  std::vector<vpiHandle> args = ScanAll(vpi_iterate(vpiArgument, &let_expr));
  ASSERT_EQ(args.size(), 2u);
  EXPECT_EQ(args[0], &a0);
  EXPECT_EQ(args[1], &default1);
}

// §37.57 (figure): the let declaration a let expression instantiates is reached
// by the diagram's tagless edge, and carries the name the declaration was
// written with. The declaration is not one of the arguments.
TEST_F(LetExprIteration, TheLetExpressionReachesTheDeclarationItInstantiates) {
  VpiObject decl;
  decl.type = vpiLetDecl;
  decl.name = "in_range";

  VpiObject let_expr;
  let_expr.type = vpiLetExpr;
  let_expr.children = {&decl};

  EXPECT_EQ(vpi_handle(vpiLetDecl, &let_expr), &decl);
  EXPECT_STREQ(vpi_get_str(vpiName, &decl), "in_range");
  EXPECT_EQ(vpi_iterate(vpiArgument, &let_expr), nullptr);
}

}  // namespace
}  // namespace delta
