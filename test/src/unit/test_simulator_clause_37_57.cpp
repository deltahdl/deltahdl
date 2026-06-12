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

}  // namespace
}  // namespace delta
