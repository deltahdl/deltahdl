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

TEST(LetExprModel, ArgumentsFollowFormalOrderAndFillDefaults) {
  VpiObject a0;
  VpiObject a2;
  VpiObject def1;

  std::vector<VpiLetFormal> formals = {
      {nullptr},
      {&def1},
      {nullptr},
  };
  std::vector<VpiHandle> provided = {&a0, nullptr, &a2};

  auto args = VpiLetExprArguments(formals, provided);
  ASSERT_EQ(args.size(), 3u);
  EXPECT_EQ(args[0], &a0);
  EXPECT_EQ(args[1], &def1);
  EXPECT_EQ(args[2], &a2);
}

TEST(LetExprModel, OmittedArgumentWithoutDefaultIsNull) {
  VpiObject a2;

  std::vector<VpiLetFormal> formals = {
      {nullptr},
      {nullptr},
  };
  std::vector<VpiHandle> provided = {nullptr, &a2};

  auto args = VpiLetExprArguments(formals, provided);
  ASSERT_EQ(args.size(), 2u);
  EXPECT_EQ(args[0], nullptr);
  EXPECT_EQ(args[1], &a2);
}

TEST(LetExprModel, FewerProvidedThanFormalsUsesDefaults) {
  VpiObject a0;
  VpiObject def1;

  std::vector<VpiLetFormal> formals = {
      {nullptr},
      {&def1},
  };
  std::vector<VpiHandle> provided = {&a0};

  auto args = VpiLetExprArguments(formals, provided);
  ASSERT_EQ(args.size(), 2u);
  EXPECT_EQ(args[0], &a0);
  EXPECT_EQ(args[1], &def1);
}

TEST(LetExprModel, NoFormalsYieldsNoArguments) {
  VpiObject stray;
  std::vector<VpiLetFormal> formals;
  std::vector<VpiHandle> provided = {&stray};

  EXPECT_TRUE(VpiLetExprArguments(formals, provided).empty());
}

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

class LetsOfARun : public VpiDesignRun {
 protected:
  static std::vector<vpiHandle> AssignedRhs(vpiHandle scope) {
    std::vector<vpiHandle> sides;
    vpiHandle it = vpi_iterate(vpiContAssign, scope);
    while (vpiHandle assign = it == nullptr ? nullptr : vpi_scan(it)) {
      sides.push_back(vpi_handle(vpiRhs, assign));
    }
    return sides;
  }

  static VpiObject* DeclOf(vpiHandle used) {
    if (used == nullptr || vpi_get(vpiType, used) != vpiLetExpr) return nullptr;
    return VpiObjectOf(vpi_handle(vpiLetDecl, used));
  }

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

TEST_F(LetsOfARun, APackagesLetIsALetDeclOfThePackage) {
  Run("package pk; let f(x) = x + 1; let h(x) = x - 1; endpackage\n"
      "package qk; let q(x) = x; endpackage\n"
      "module top; import pk::f; import qk::*;\n"
      "  logic [3:0] a, w, v, z, s;\n"
      "  function automatic int fn(int x); return x; endfunction\n"
      "  assign w = f(a);\n"
      "  assign v = pk::h(a);\n"
      "  assign z = q(a);\n"
      "  assign s = fn(a);\n"
      "endmodule\n");
  vpiHandle pk = By("pk");
  ASSERT_NE(pk, nullptr);
  std::vector<std::string> names = NamesOf(vpiLetDecl, pk);
  std::ranges::sort(names);
  EXPECT_EQ(names, (std::vector<std::string>{"f", "h"}));
  vpiHandle qk = By("qk");
  ASSERT_NE(qk, nullptr);
  EXPECT_EQ(NamesOf(vpiLetDecl, qk), (std::vector<std::string>{"q"}));
  const std::vector<vpiHandle> kSides = AssignedRhs(By("top"));
  ASSERT_EQ(kSides.size(), 4U);
  EXPECT_EQ(DeclOf(kSides[0]), VpiObjectOf(Named(vpiLetDecl, pk, "f")));
  EXPECT_EQ(DeclOf(kSides[1]), VpiObjectOf(Named(vpiLetDecl, pk, "h")));
  EXPECT_EQ(DeclOf(kSides[2]), VpiObjectOf(Named(vpiLetDecl, qk, "q")));
  ASSERT_NE(kSides[3], nullptr);
  EXPECT_EQ(vpi_get(vpiType, kSides[3]), vpiFuncCall);
}

TEST_F(LetsOfARun, ACompilationUnitsLetIsALetDeclOfItsScope) {
  Run("let g(y) = y * 2;\n"
      "module top; logic [3:0] a, w; assign w = g(a); endmodule\n");
  vpiHandle unit = Named(vpiPackage, nullptr, "$unit");
  ASSERT_NE(unit, nullptr);
  EXPECT_EQ(NamesOf(vpiLetDecl, unit), (std::vector<std::string>{"g"}));
  const std::vector<vpiHandle> kSides = AssignedRhs(By("top"));
  ASSERT_EQ(kSides.size(), 1U);
  EXPECT_EQ(DeclOf(kSides[0]), VpiObjectOf(Named(vpiLetDecl, unit, "g")));
}

}  // namespace
}  // namespace delta
