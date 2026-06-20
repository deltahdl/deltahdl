#include <cstdint>
#include <cstring>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_string_var.h"
#include "parser/ast.h"
#include "simulator/adv_sim.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(StringConcatAndReplication, StringConcatValue) {
  SimFixture f;
  MakeStringVar(f, "s1", "hello");
  MakeStringVar(f, "s2", " world");
  auto* concat = f.arena.Create<Expr>();
  concat->kind = ExprKind::kConcatenation;
  concat->elements.push_back(MakeId(f.arena, "s1"));
  concat->elements.push_back(MakeId(f.arena, "s2"));
  auto result = EvalExpr(concat, f.ctx, f.arena);
  EXPECT_EQ(VecToStr(result), "hello world");
}

TEST(StringConcatAndReplication, StringReplicateValue) {
  SimFixture f;
  MakeStringVar(f, "sr", "ab");
  auto* repl = f.arena.Create<Expr>();
  repl->kind = ExprKind::kReplicate;
  repl->repeat_count = MakeInt(f.arena, 3);
  repl->elements.push_back(MakeId(f.arena, "sr"));
  auto result = EvalExpr(repl, f.ctx, f.arena);
  EXPECT_EQ(VecToStr(result), "ababab");
}

TEST(StringConcatAndReplication, StringConcatSetsIsString) {
  SimFixture f;
  MakeStringVar(f, "sa", "hi");
  MakeStringVar(f, "sb", "lo");
  auto* concat = f.arena.Create<Expr>();
  concat->kind = ExprKind::kConcatenation;
  concat->elements.push_back(MakeId(f.arena, "sa"));
  concat->elements.push_back(MakeId(f.arena, "sb"));
  auto result = EvalExpr(concat, f.ctx, f.arena);
  EXPECT_TRUE(result.is_string);
}

TEST(StringConcatAndReplication, NonStringConcatNotIsString) {
  SimFixture f;
  auto* a = f.ctx.CreateVariable("ia", 8);
  a->value = MakeLogic4VecVal(f.arena, 8, 0x41);
  auto* b = f.ctx.CreateVariable("ib", 8);
  b->value = MakeLogic4VecVal(f.arena, 8, 0x42);
  auto* concat = f.arena.Create<Expr>();
  concat->kind = ExprKind::kConcatenation;
  concat->elements.push_back(MakeId(f.arena, "ia"));
  concat->elements.push_back(MakeId(f.arena, "ib"));
  auto result = EvalExpr(concat, f.ctx, f.arena);
  EXPECT_FALSE(result.is_string);
}

TEST(StringConcatAndReplication, StringReplicateSetsIsString) {
  SimFixture f;
  MakeStringVar(f, "sr2", "ab");
  auto* repl = f.arena.Create<Expr>();
  repl->kind = ExprKind::kReplicate;
  repl->repeat_count = MakeInt(f.arena, 2);
  repl->elements.push_back(MakeId(f.arena, "sr2"));
  auto result = EvalExpr(repl, f.ctx, f.arena);
  EXPECT_TRUE(result.is_string);
}

TEST(StringConcatAndReplication, MixedStringAndIntegralConcatIsString) {
  SimFixture f;
  MakeStringVar(f, "sv", "hi");
  auto* iv = f.ctx.CreateVariable("iv", 8);
  iv->value = MakeLogic4VecVal(f.arena, 8, 0x41);
  auto* concat = f.arena.Create<Expr>();
  concat->kind = ExprKind::kConcatenation;
  concat->elements.push_back(MakeId(f.arena, "sv"));
  concat->elements.push_back(MakeId(f.arena, "iv"));
  auto result = EvalExpr(concat, f.ctx, f.arena);
  EXPECT_TRUE(result.is_string);
}

TEST(StringConcatAndReplication, SingleStringConcatValue) {
  SimFixture f;
  MakeStringVar(f, "s", "only");
  auto* concat = f.arena.Create<Expr>();
  concat->kind = ExprKind::kConcatenation;
  concat->elements.push_back(MakeId(f.arena, "s"));
  auto result = EvalExpr(concat, f.ctx, f.arena);
  EXPECT_TRUE(result.is_string);
  EXPECT_EQ(VecToStr(result), "only");
}

TEST(StringConcatAndReplication, StringReplicateOne) {
  SimFixture f;
  MakeStringVar(f, "s", "abc");
  auto* repl = f.arena.Create<Expr>();
  repl->kind = ExprKind::kReplicate;
  repl->repeat_count = MakeInt(f.arena, 1);
  repl->elements.push_back(MakeId(f.arena, "s"));
  auto result = EvalExpr(repl, f.ctx, f.arena);
  EXPECT_TRUE(result.is_string);
  EXPECT_EQ(VecToStr(result), "abc");
}

TEST(StringConcatAndReplication, EndToEndStringConcat) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string a, b, c;\n"
      "  initial begin\n"
      "    a = \"hello\";\n"
      "    b = \" world\";\n"
      "    c = {a, b};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("c");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(VecToStr(var->value), "hello world");
}

TEST(StringConcatAndReplication, EndToEndStringReplication) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string s;\n"
      "  initial s = {3{\"ab\"}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("s");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(VecToStr(var->value), "ababab");
}

TEST(StringConcatAndReplication, EndToEndStringConcatAppend) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string s;\n"
      "  initial begin\n"
      "    s = \"hello\";\n"
      "    s = {s, \" and goodbye\"};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("s");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(VecToStr(var->value), "hello and goodbye");
}

TEST(StringConcatAndReplication, EndToEndNoTruncation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string s;\n"
      "  initial begin\n"
      "    s = \"hi\";\n"
      "    s = {s, \" there everyone\"};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("s");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(VecToStr(var->value), "hi there everyone");
}

TEST(StringConcatAndReplication, EndToEndNonConstantMultiplier) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    int n;\n"
      "    string s;\n"
      "    n = 3;\n"
      "    s = {n{\"boo \"}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("s");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(VecToStr(var->value), "boo boo boo ");
}

TEST(StringConcatAndReplication, EndToEndThreeStringConcat) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string hello, s;\n"
      "  initial begin\n"
      "    hello = \"hello\";\n"
      "    s = {hello, \" \", \"world\"};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("s");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(VecToStr(var->value), "hello world");
}

}  // namespace
