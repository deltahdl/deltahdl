#include <gtest/gtest.h>

#include <algorithm>
#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

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
  EXPECT_EQ(args[1],
            &def1);  // default substituted, declaration order kept
  EXPECT_EQ(args[2], &a2);
}

// §37.57 detail 1 (an argument the instantiation leaves out, when the formal
// has no default): an omitted argument whose formal has no default value yields
// a null argument in that position, so later arguments still align with their
// own formals rather than shifting left.
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
  EXPECT_EQ(args[1],
            &def1);  // trailing formal filled from its default
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

  std::vector<vpiHandle> args =
      ScanAll(vpi_iterate(vpiArgument, VpiHandleOf(&let_expr)));
  ASSERT_EQ(args.size(), 2u);
  EXPECT_EQ(VpiObjectOf(args[0]), &a0);
  EXPECT_EQ(VpiObjectOf(args[1]), &a1);
}

// §37.57 detail 1: when the instantiation gives a formal with a default no
// value, the default appears as its argument. The instantiation leaves the
// first port empty - written the way §37.42 detail 8 writes an omitted argument
// - so the formal's default stands in its place and the actual it did write
// keeps the second position.
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

  std::vector<vpiHandle> args =
      ScanAll(vpi_iterate(vpiArgument, VpiHandleOf(&let_expr)));
  ASSERT_EQ(args.size(), 2u);
  EXPECT_EQ(VpiObjectOf(args[0]), &default0);
  EXPECT_EQ(VpiObjectOf(args[1]), &a1);
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

  std::vector<vpiHandle> args =
      ScanAll(vpi_iterate(vpiArgument, VpiHandleOf(&let_expr)));
  ASSERT_EQ(args.size(), 2u);
  EXPECT_EQ(VpiObjectOf(args[0]), &a0);
  EXPECT_EQ(VpiObjectOf(args[1]), &default1);
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

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLetDecl, VpiHandleOf(&let_expr))), &decl);
  EXPECT_STREQ(vpi_get_str(vpiName, VpiHandleOf(&decl)), "in_range");
  EXPECT_EQ(vpi_iterate(vpiArgument, VpiHandleOf(&let_expr)), nullptr);
}

// §37.57 detail 1: an operation the instantiation wrote is an argument like
// any other expression; a child of the let expression that is neither its
// declaration nor an expression is none; and a formal left empty with no
// default has no argument object, so the iteration hands back the rest.
TEST_F(LetExprIteration, OnlyWrittenAndDefaultedArgumentsComeBack) {
  VpiObject formal0;
  formal0.type = vpiSeqFormalDecl;
  VpiObject formal1;
  formal1.type = vpiSeqFormalDecl;
  VpiObject decl;
  decl.type = vpiLetDecl;
  decl.children = {&formal0, &formal1};

  VpiObject sum;
  sum.type = vpiOperation;
  sum.op_type = vpiAddOp;
  VpiObject attribute;
  attribute.type = vpiAttribute;
  VpiObject omitted;
  VpiMakeEmptyArgument(&omitted);

  VpiObject let_expr;
  let_expr.type = vpiLetExpr;
  let_expr.children = {&decl, &sum, &attribute, &omitted};

  std::vector<vpiHandle> args =
      ScanAll(vpi_iterate(vpiArgument, VpiHandleOf(&let_expr)));
  ASSERT_EQ(args.size(), 1u);
  EXPECT_EQ(VpiObjectOf(args[0]), &sum);
}

// §37.57 detail 1: a null formal has no default, and a formal's default is its
// first expression child, its typespec not being one.
TEST(LetFormalDefault, NullHasNoneAndTheTypespecIsPassedOver) {
  EXPECT_EQ(VpiLetFormalDefault(nullptr), nullptr);
  VpiObject typespec;
  typespec.type = vpiTypespec;
  VpiObject value;
  value.type = vpiConstant;
  VpiObject formal;
  formal.type = vpiSeqFormalDecl;
  formal.children = {&typespec, &value};
  EXPECT_EQ(VpiLetFormalDefault(&formal), &value);
}

// The lets of a run, built from the elaborated design.
class LetsOfARun : public VpiDesignRun {
 protected:
  // The kinds of what the vpiArgument iteration of `let_expr` reaches, in
  // the order reached.
  static std::vector<int> ArgumentKinds(vpiHandle let_expr) {
    std::vector<int> kinds;
    vpiHandle it = vpi_iterate(vpiArgument, let_expr);
    while (vpiHandle arg = it == nullptr ? nullptr : vpi_scan(it)) {
      kinds.push_back(vpi_get(vpiType, arg));
    }
    return kinds;
  }
};

constexpr const char* kLets =
    "module top; logic a, b, clk; logic [3:0] w; int r;\n"
    "  let pick(x = 2, y) = x + y;\n"
    "  let one = 1;\n"
    "  covergroup cg @(posedge clk); coverpoint a; endgroup\n"
    "  assign w = pick(a, b);\n"
    "  initial r = pick(, b) + one;\n"
    "endmodule\n";

// §37.12 with the let decl of the figure: each let a module declares is a let
// decl of its instance, named after it, reaching a seq formal decl per formal
// in the order declared, each reaching the default it declares, if any, and
// its body, in which a formal's name is a ref obj named after it and bound to
// no actual, as in a sequence's body (§37.53); a covergroup beside the lets
// is none (#7036).
TEST_F(LetsOfARun, AModulesLetsAreLetDeclsOfItsInstance) {
  Run(kLets);
  vpiHandle top = By("top");
  std::vector<std::string> names = NamesOf(vpiLetDecl, top);
  std::ranges::sort(names);
  EXPECT_EQ(names, (std::vector<std::string>{"one", "pick"}));
  vpiHandle pick = Named(vpiLetDecl, top, "pick");
  ASSERT_NE(pick, nullptr);
  EXPECT_EQ(NamesOf(vpiSeqFormalDecl, pick),
            (std::vector<std::string>{"x", "y"}));
  vpiHandle x = vpi_handle(vpiExpr, Named(vpiSeqFormalDecl, pick, "x"));
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(vpi_get(vpiType, x), vpiConstant);
  EXPECT_EQ(vpi_handle(vpiExpr, Named(vpiSeqFormalDecl, pick, "y")), nullptr);
  vpiHandle body = vpi_handle(vpiExpr, pick);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(vpi_get(vpiOpType, body), vpiAddOp);
  const std::vector<vpiHandle> kOperands = OperandsOf(body);
  ASSERT_EQ(kOperands.size(), 2U);
  for (vpiHandle operand : kOperands) {
    EXPECT_EQ(vpi_get(vpiType, operand), vpiRefObj);
    EXPECT_EQ(vpi_handle(vpiActual, operand), nullptr);
  }
  EXPECT_STREQ(vpi_get_str(vpiName, kOperands[1]), "y");
}

// The let expr of the figure: a use of a let, called with arguments in a
// continuous assignment or by its name alone in a procedure, is a let expr
// reaching the let decl it instantiates and, through vpiArgument, an argument
// per formal in the order declared, an omitted one its formal's default
// (detail 1) (#7185).
TEST_F(LetsOfARun, AUseOfALetIsALetExpr) {
  Run(kLets);
  vpiHandle top = By("top");
  vpiHandle assigns = vpi_iterate(vpiContAssign, top);
  vpiHandle assign = assigns == nullptr ? nullptr : vpi_scan(assigns);
  ASSERT_NE(assign, nullptr);
  vpiHandle called = vpi_handle(vpiRhs, assign);
  ASSERT_NE(called, nullptr);
  EXPECT_EQ(vpi_get(vpiType, called), vpiLetExpr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLetDecl, called)),
            VpiObjectOf(Named(vpiLetDecl, top, "pick")));
  EXPECT_EQ(NamesOf(vpiArgument, called), (std::vector<std::string>{"a", "b"}));
  vpiHandle procs = vpi_iterate(vpiProcess, top);
  vpiHandle proc = procs == nullptr ? nullptr : vpi_scan(procs);
  ASSERT_NE(proc, nullptr);
  vpiHandle sum = vpi_handle(vpiRhs, vpi_handle(vpiStmt, proc));
  ASSERT_NE(sum, nullptr);
  const std::vector<vpiHandle> kUses = OperandsOf(sum);
  ASSERT_EQ(kUses.size(), 2U);
  EXPECT_EQ(vpi_get(vpiType, kUses[0]), vpiLetExpr);
  const std::vector<int> kPicked = ArgumentKinds(kUses[0]);
  ASSERT_EQ(kPicked.size(), 2U);
  EXPECT_EQ(kPicked[0], vpiConstant);
  EXPECT_NE(kPicked[1], vpiConstant);
  EXPECT_EQ(vpi_get(vpiType, kUses[1]), vpiLetExpr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLetDecl, kUses[1])),
            VpiObjectOf(Named(vpiLetDecl, top, "one")));
  EXPECT_TRUE(ArgumentKinds(kUses[1]).empty());
}

// §37.12 with §37.85 and §27.4: a let a generate block declares is a let decl
// of the gen scope of the block instance declaring it, one per instance of a
// loop generate block, and of no scope around it; a use of it in the block is
// a let expr reaching it (#7322).
TEST_F(LetsOfARun, AGenerateBlocksLetIsALetDeclOfItsGenScope) {
  Run("module top; logic a, w, v;\n"
      "  let h(x) = x;\n"
      "  if (1) begin : g\n"
      "    let f(x) = x + 1;\n"
      "    assign w = f(a);\n"
      "  end\n"
      "  for (genvar i = 0; i < 2; i++) begin : l\n"
      "    let k(x) = x;\n"
      "  end\n"
      "  assign v = h(a);\n"
      "endmodule\n");
  EXPECT_EQ(NamesOf(vpiLetDecl, By("top")), (std::vector<std::string>{"h"}));
  vpiHandle g = By("top.g");
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(NamesOf(vpiLetDecl, g), (std::vector<std::string>{"f"}));
  for (const char* block : {"top.l[0]", "top.l[1]"}) {
    EXPECT_EQ(NamesOf(vpiLetDecl, By(block)), (std::vector<std::string>{"k"}))
        << block;
  }
  vpiHandle assigns = vpi_iterate(vpiContAssign, g);
  vpiHandle assign = assigns == nullptr ? nullptr : vpi_scan(assigns);
  ASSERT_NE(assign, nullptr);
  vpiHandle used = vpi_handle(vpiRhs, assign);
  ASSERT_NE(used, nullptr);
  EXPECT_EQ(vpi_get(vpiType, used), vpiLetExpr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLetDecl, used)),
            VpiObjectOf(Named(vpiLetDecl, g, "f")));
}

}  // namespace
}  // namespace delta
