#include <cstring>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;

static ModuleItem* MakeLetDecl(Arena& arena, std::string_view name, Expr* body,
                               std::vector<FunctionArg> args = {}) {
  auto* item = arena.Create<ModuleItem>();
  item->kind = ModuleItemKind::kLetDecl;
  item->name = name;
  item->init_expr = body;
  item->func_args = std::move(args);
  return item;
}

namespace {

TEST(LetExpansionSimulation, LetRecursionGuard) {
  SimFixture f;

  auto* body_call = MakeCall(f.arena, "bad", {[&]() {
                               auto* e = f.arena.Create<Expr>();
                               e->kind = ExprKind::kBinary;
                               e->op = TokenKind::kPlus;
                               e->lhs = MakeId(f.arena, "a");
                               e->rhs = MakeInt(f.arena, 1);
                               return e;
                             }()});
  FunctionArg arg;
  arg.name = "a";
  auto* decl = MakeLetDecl(f.arena, "bad", body_call, {arg});
  f.ctx.RegisterLetDecl("bad", decl);

  auto* call = MakeCall(f.arena, "bad", {MakeInt(f.arena, 0)});
  auto result = EvalExpr(call, f.ctx, f.arena);

  EXPECT_TRUE(result.nwords > 0);
}

static Expr* SLMakeId(Arena& arena, std::string_view name) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

static Expr* SLMakeSysCall(Arena& arena, std::string_view callee,
                           std::vector<Expr*> args) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kSystemCall;
  e->callee = callee;
  e->args = std::move(args);
  return e;
}

static Expr* SLMakeCall(Arena& arena, std::string_view callee,
                        std::vector<Expr*> args) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kCall;
  e->callee = callee;
  e->args = std::move(args);
  return e;
}

static ModuleItem* SLMakeLetDecl(Arena& arena, std::string_view name,
                                 Expr* body,
                                 std::vector<FunctionArg> args = {}) {
  auto* item = arena.Create<ModuleItem>();
  item->kind = ModuleItemKind::kLetDecl;
  item->name = name;
  item->init_expr = body;
  item->func_args = std::move(args);
  return item;
}

TEST(LetExpansionSimulation, LetWithPastInBody) {
  SampledLetFixture f;

  FunctionArg arg;
  arg.name = "x";
  auto* body = SLMakeSysCall(f.arena, "$past", {SLMakeId(f.arena, "x")});
  auto* decl = SLMakeLetDecl(f.arena, "get_past", body, {arg});
  f.ctx.RegisterLetDecl("get_past", decl);

  auto* var = f.ctx.CreateVariable("sig", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 42);

  auto* call = SLMakeCall(f.arena, "get_past", {SLMakeId(f.arena, "sig")});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

TEST(LetExpansionSimulation, LetWithChangedInBody) {
  SampledLetFixture f;

  FunctionArg arg;
  arg.name = "x";
  auto* body = SLMakeSysCall(f.arena, "$changed", {SLMakeId(f.arena, "x")});
  auto* decl = SLMakeLetDecl(f.arena, "check_changed", body, {arg});
  f.ctx.RegisterLetDecl("check_changed", decl);

  auto* var = f.ctx.CreateVariable("sig2", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 5);

  auto* call =
      SLMakeCall(f.arena, "check_changed", {SLMakeId(f.arena, "sig2")});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(LetExpansionSimulation, LetWithSampledInBody) {
  SampledLetFixture f;

  FunctionArg arg;
  arg.name = "x";
  auto* body = SLMakeSysCall(f.arena, "$sampled", {SLMakeId(f.arena, "x")});
  auto* decl = SLMakeLetDecl(f.arena, "get_sampled", body, {arg});
  f.ctx.RegisterLetDecl("get_sampled", decl);

  auto* var = f.ctx.CreateVariable("sig3", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 99);

  auto* call = SLMakeCall(f.arena, "get_sampled", {SLMakeId(f.arena, "sig3")});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 99u);
}

TEST(LetExpansionSimulation, LetExpandMultipleArgs) {
  SimFixture f;

  FunctionArg arg_a;
  arg_a.name = "a";
  FunctionArg arg_b;
  arg_b.name = "b";
  FunctionArg arg_c;
  arg_c.name = "c";
  auto* body = f.arena.Create<Expr>();
  body->kind = ExprKind::kBinary;
  body->op = TokenKind::kPlus;
  body->lhs = MakeId(f.arena, "a");
  auto* rhs = f.arena.Create<Expr>();
  rhs->kind = ExprKind::kBinary;
  rhs->op = TokenKind::kPlus;
  rhs->lhs = MakeId(f.arena, "b");
  rhs->rhs = MakeId(f.arena, "c");
  body->rhs = rhs;
  auto* decl = MakeLetDecl(f.arena, "sum3", body, {arg_a, arg_b, arg_c});
  f.ctx.RegisterLetDecl("sum3", decl);

  auto* call = MakeCall(
      f.arena, "sum3",
      {MakeInt(f.arena, 10), MakeInt(f.arena, 20), MakeInt(f.arena, 30)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 60u);
}

TEST(LetExpansionSimulation, LetExpandAllDefaults) {
  SimFixture f;

  FunctionArg arg_a;
  arg_a.name = "a";
  arg_a.default_value = MakeInt(f.arena, 7);
  FunctionArg arg_b;
  arg_b.name = "b";
  arg_b.default_value = MakeInt(f.arena, 3);
  auto* body = f.arena.Create<Expr>();
  body->kind = ExprKind::kBinary;
  body->op = TokenKind::kPlus;
  body->lhs = MakeId(f.arena, "a");
  body->rhs = MakeId(f.arena, "b");
  auto* decl = MakeLetDecl(f.arena, "def_add", body, {arg_a, arg_b});
  f.ctx.RegisterLetDecl("def_add", decl);

  auto* call = MakeCall(f.arena, "def_add", {});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 10u);
}

TEST(LetExpansionSimulation, EndToEndLetCallInInitialBlock) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  let add(a, b) = a + b;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = add(10, 20);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

TEST(LetExpansionSimulation, EndToEndLetNoArgs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  let magic = 42;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = magic;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(LetExpansionSimulation, EndToEndLetWithDefault) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  let inc(x, step = 1) = x + step;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    r1 = inc(10);\n"
      "    r2 = inc(10, 5);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* v1 = f.ctx.FindVariable("r1");
  auto* v2 = f.ctx.FindVariable("r2");
  ASSERT_NE(v1, nullptr);
  ASSERT_NE(v2, nullptr);
  EXPECT_EQ(v1->value.ToUint64(), 11u);
  EXPECT_EQ(v2->value.ToUint64(), 15u);
}

TEST(LetExpansionSimulation, EndToEndLetTernaryBody) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  let max(a, b) = (a > b) ? a : b;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    r1 = max(3, 7);\n"
      "    r2 = max(10, 2);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* v1 = f.ctx.FindVariable("r1");
  auto* v2 = f.ctx.FindVariable("r2");
  ASSERT_NE(v1, nullptr);
  ASSERT_NE(v2, nullptr);
  EXPECT_EQ(v1->value.ToUint64(), 7u);
  EXPECT_EQ(v2->value.ToUint64(), 10u);
}

TEST(LetExpansionSimulation, EndToEndLetMultipleDecls) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  let add(a, b) = a + b;\n"
      "  let sub(a, b) = a - b;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    r1 = add(10, 3);\n"
      "    r2 = sub(10, 3);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* v1 = f.ctx.FindVariable("r1");
  auto* v2 = f.ctx.FindVariable("r2");
  ASSERT_NE(v1, nullptr);
  ASSERT_NE(v2, nullptr);
  EXPECT_EQ(v1->value.ToUint64(), 13u);
  EXPECT_EQ(v2->value.ToUint64(), 7u);
}

TEST(LetExpansionSimulation, EndToEndLetNestedCalls) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  let inc(x) = x + 1;\n"
      "  let dbl(x) = x * 2;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = dbl(inc(3));\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 8u);
}

TEST(LetExpansionSimulation, EndToEndLetParenthesizedPrecedence) {
  SimFixture f;

  auto* design = ElaborateSrc(
      "module t;\n"
      "  let add(a, b) = a + b;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = add(2, 3) * 4;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(LetExpansionSimulation, EndToEndTypedFormalCastsActualToFormalWidth) {
  SimFixture f;
  // §11.12 rule 2: the actual for a non-event typed formal is cast to the
  // formal's type before it is substituted into the body. The 4-bit formal
  // narrows 8'd255 to 4'hF, so the let body sees 15, not 255.
  auto* design = ElaborateSrc(
      "module t;\n"
      "  let low4(logic [3:0] x) = x;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = low4(8'd255);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 15u);
}

TEST(LetExpansionSimulation, EndToEndUntypedFormalDoesNotCastActual) {
  SimFixture f;
  // §11.12: the cast applies only to typed formals. An untyped formal carries
  // the full actual value through unchanged, so all 8 bits of 8'd255 survive.
  auto* design = ElaborateSrc(
      "module t;\n"
      "  let pass(x) = x;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = pass(8'd255);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 255u);
}

TEST(LetExpansionSimulation, EndToEndTwoStateFormalDrivesXZActualBitsToZero) {
  SimFixture f;
  // §11.12 rule 2 / example e: the actual for a non-event typed formal is cast
  // to the formal's type before substitution. A `bit` formal is 2-state, so
  // every unknown (x) or high-impedance (z) bit of the actual becomes 0. Here
  // the actual 8'b101010xz has x/z in its two low bits; after the cast they
  // read as 0, leaving the fully-known value 8'b10101000 (0xA8). The result is
  // held in a 4-state `logic` so the coercion is observable — a 2-state
  // destination would mask it.
  auto* design = ElaborateSrc(
      "module t;\n"
      "  let low(bit [7:0] x) = x;\n"
      "  logic [7:0] src;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    src = 8'b101010xz;\n"
      "    result = low(src);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToUint64(), 0xA8u);
}

TEST(LetExpansionSimulation, LetDeclarativeScopeIgnoresInstantiationVar) {
  SimFixture f;

  MakeVar(f, "K", 32, 42);

  auto* body = MakeId(f.arena, "K");
  auto* decl = MakeLetDecl(f.arena, "get_k", body);
  f.ctx.RegisterLetDecl("get_k", decl);

  f.ctx.PushScope();
  auto* local_k = f.ctx.CreateLocalVariable("K", 32);
  local_k->value = MakeLogic4VecVal(f.arena, 32, 999);

  auto* call = MakeCall(f.arena, "get_k", {});
  auto result = EvalExpr(call, f.ctx, f.arena);

  f.ctx.PopScope();

  EXPECT_EQ(result.ToUint64(), 42u);
}

TEST(LetExpansionSimulation, EndToEndLetNamedArgs) {
  SimFixture f;
  // §11.12: expansion binds each actual to its formal. Here the actuals are
  // supplied by name out of declaration order, so correct binding requires
  // matching on formal name, not position: sub = a - b = 10 - 3 = 7.
  auto* design = ElaborateSrc(
      "module t;\n"
      "  let sub(a, b) = a - b;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = sub(.b(3), .a(10));\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

TEST(LetExpansionSimulation, EndToEndLetMixedPositionalAndNamedArgs) {
  SimFixture f;
  // §11.12: a let call may mix a leading positional actual with trailing named
  // actuals; each still binds to the intended formal. a=1 (positional), b=2,
  // c=3 (named) → 1 + 2 + 3 = 6.
  auto* design = ElaborateSrc(
      "module t;\n"
      "  let f(a, b, c) = a + b + c;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = f(1, .c(3), .b(2));\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 6u);
}

TEST(LetExpansionSimulation, EndToEndLetNamedActualLeavesDefaultInPlace) {
  SimFixture f;
  // §11.12: a default actual declared in the let fills any formal the call
  // omits, including when the supplied actuals are named. Calling with only
  // .a(5) leaves b at its default 10, so the body yields 15.
  auto* design = ElaborateSrc(
      "module t;\n"
      "  let f(a, b = 10) = a + b;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = f(.a(5));\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 15u);
}

TEST(LetExpansionSimulation, EndToEndLetAllDefaultsCallOmitsAllActuals) {
  SimFixture f;
  // §11.12: when every formal carries a default actual, a call that supplies no
  // actuals at all binds each formal to its default. This is the boundary input
  // form of the default rule — the call site is empty parens on a let that has
  // formals, distinct from a no-formal let. Both defaults apply: 7 + 3 = 10.
  auto* design = ElaborateSrc(
      "module t;\n"
      "  let f(a = 7, b = 3) = a + b;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = f();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(LetExpansionSimulation, EndToEndLetBodyWithSampledValueCall) {
  SimFixture f;
  // §11.12: a let body may contain sampled value function calls (§16.9.3,
  // §16.9.4). This builds that dependency from real source — a let whose body
  // is $sampled(x) — and drives it through the full pipeline rather than
  // hand-building the call AST. Expanding and evaluating the call in the
  // instantiation context yields the argument's value (99).
  auto* design = ElaborateSrc(
      "module t;\n"
      "  let get_sampled(x) = $sampled(x);\n"
      "  logic [31:0] sig;\n"
      "  int result;\n"
      "  initial begin\n"
      "    sig = 99;\n"
      "    result = get_sampled(sig);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(LetExpansionSimulation, EndToEndRecursiveLetInstantiationIsReported) {
  SimFixture f;
  // §11.12: recursive let instantiations are not permitted. A let whose body
  // instantiates itself is built from real source and driven through the full
  // pipeline; the design elaborates (the self-reference is not resolved until
  // expansion), and when the initial block evaluates the call, the simulator
  // detects the recursion and reports it as an error rather than expanding it
  // without bound.
  auto* design = ElaborateSrc(
      "module t;\n"
      "  let r(x) = r(x) + 1;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = r(3);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
