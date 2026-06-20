#include "builders_ast.h"
#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// Creates an automatic function with a single const-ref `data` argument and an
// empty body. Shared setup for the const-ref write-protection tests below.
static ModuleItem* MakeConstRefDataFunc(SimFixture& f, const char* name) {
  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = name;
  func->is_automatic = true;
  func->func_args = {
      {Direction::kRef, true, false, false, {}, "data", nullptr, {}}};
  return func;
}

TEST(PassByRefValidation, RejectRefInStaticFunc) {
  SimFixture f;

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "bad_func";
  func->is_static = true;
  func->is_automatic = false;
  func->func_args = {
      {Direction::kRef, false, false, false, {}, "v", nullptr, {}}};

  ValidateRefLifetime(func, f.diag);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PassByRefValidation, AcceptRefInAutoFunc) {
  SimFixture f;

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "good_func";
  func->is_automatic = true;
  func->func_args = {
      {Direction::kRef, false, false, false, {}, "v", nullptr, {}}};

  ValidateRefLifetime(func, f.diag);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PassByRefValidation, ConstRefArgAccepted) {
  SimFixture f;

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "read_only";
  func->is_automatic = true;
  func->func_args = {
      {Direction::kRef, true, false, false, {}, "data", nullptr, {}}};

  ValidateRefLifetime(func, f.diag);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PassByRefValidation, RejectRefInStaticTask) {
  SimFixture f;

  auto* task = f.arena.Create<ModuleItem>();
  task->kind = ModuleItemKind::kTaskDecl;
  task->name = "bad_task";
  task->is_static = true;
  task->is_automatic = false;
  task->func_args = {
      {Direction::kRef, false, false, false, {}, "v", nullptr, {}}};

  ValidateRefLifetime(task, f.diag);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PassByRefValidation, ConstRefInStaticSubroutineRejected) {
  SimFixture f;

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "bad_func";
  func->is_static = true;
  func->is_automatic = false;
  func->func_args = {
      {Direction::kRef, true, false, false, {}, "data", nullptr, {}}};

  ValidateRefLifetime(func, f.diag);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PassByRefValidation, MultipleRefArgsInStaticFuncAllRejected) {
  SimFixture f;

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "bad_func";
  func->is_static = true;
  func->is_automatic = false;
  func->func_args = {
      {Direction::kRef, false, false, false, {}, "a", nullptr, {}},
      {Direction::kInput, false, false, false, {}, "b", nullptr, {}},
      {Direction::kRef, false, false, false, {}, "c", nullptr, {}},
  };

  ValidateRefLifetime(func, f.diag);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PassByRefValidation, NetActualPassedByRefRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire w;\n"
      "  function automatic void take(ref logic v);\n"
      "  endfunction\n"
      "  initial take(w);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(PassByRefValidation, NetSelectPassedByRefRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire [7:0] w;\n"
      "  function automatic void take(ref logic v);\n"
      "  endfunction\n"
      "  initial take(w[0]);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(PassByRefValidation, NetActualPassedByConstRefRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire w;\n"
      "  function automatic int take(const ref logic v);\n"
      "    return 0;\n"
      "  endfunction\n"
      "  int x;\n"
      "  initial x = take(w);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(PassByRefValidation, VariableActualPassedByRefAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic v;\n"
      "  function automatic void take(ref logic x);\n"
      "  endfunction\n"
      "  initial take(v);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PassByRefValidation, VariableBitSelectPassedByRefAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [7:0] v;\n"
      "  function automatic void take(ref logic x);\n"
      "  endfunction\n"
      "  initial take(v[0]);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PassByRefValidation, StructMemberPassedByRefAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  struct { logic a; logic b; } s;\n"
      "  function automatic void take(ref logic x);\n"
      "  endfunction\n"
      "  initial take(s.a);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PassByRefValidation, ConstRefBlockingWriteRejected) {
  SimFixture f;

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "read_only";
  func->is_automatic = true;
  func->func_args = {
      {Direction::kRef, true, false, false, {}, "data", nullptr, {}}};
  func->func_body_stmts = {MakeAssign(f.arena, "data", MakeInt(f.arena, 7))};

  ValidateConstRefWriteProtection(func, f.diag);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PassByRefValidation, ConstRefNonblockingWriteRejected) {
  SimFixture f;

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "read_only";
  func->is_automatic = true;
  func->func_args = {
      {Direction::kRef, true, false, false, {}, "data", nullptr, {}}};
  auto* nba = f.arena.Create<Stmt>();
  nba->kind = StmtKind::kNonblockingAssign;
  nba->lhs = MakeId(f.arena, "data");
  nba->rhs = MakeInt(f.arena, 0);
  func->func_body_stmts = {nba};

  ValidateConstRefWriteProtection(func, f.diag);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PassByRefValidation, ConstRefReadOnlyAccepted) {
  SimFixture f;

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "show";
  func->is_automatic = true;
  func->func_args = {
      {Direction::kRef, true, false, false, {}, "data", nullptr, {}}};
  func->func_body_stmts = {MakeReturn(f.arena, MakeId(f.arena, "data"))};

  ValidateConstRefWriteProtection(func, f.diag);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PassByRefValidation, PlainRefWriteAccepted) {
  SimFixture f;

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "writer";
  func->is_automatic = true;
  func->func_args = {
      {Direction::kRef, false, false, false, {}, "data", nullptr, {}}};
  func->func_body_stmts = {MakeAssign(f.arena, "data", MakeInt(f.arena, 7))};

  ValidateConstRefWriteProtection(func, f.diag);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PassByRefValidation, ConstRefWriteInIfBranchRejected) {
  SimFixture f;

  auto* func = MakeConstRefDataFunc(f, "guarded_write");
  auto* if_stmt = f.arena.Create<Stmt>();
  if_stmt->kind = StmtKind::kIf;
  if_stmt->condition = MakeInt(f.arena, 1);
  if_stmt->then_branch = MakeAssign(f.arena, "data", MakeInt(f.arena, 5));
  func->func_body_stmts = {if_stmt};

  ValidateConstRefWriteProtection(func, f.diag);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PassByRefValidation, ConstRefWriteInElseBranchRejected) {
  SimFixture f;

  auto* func = MakeConstRefDataFunc(f, "guarded_write");
  auto* if_stmt = f.arena.Create<Stmt>();
  if_stmt->kind = StmtKind::kIf;
  if_stmt->condition = MakeInt(f.arena, 0);
  if_stmt->then_branch = MakeReturn(f.arena, MakeInt(f.arena, 0));
  if_stmt->else_branch = MakeAssign(f.arena, "data", MakeInt(f.arena, 9));
  func->func_body_stmts = {if_stmt};

  ValidateConstRefWriteProtection(func, f.diag);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PassByRefValidation, ConstRefWriteInCaseItemRejected) {
  SimFixture f;

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "case_write";
  func->is_automatic = true;
  func->func_args = {
      {Direction::kRef, true, false, false, {}, "data", nullptr, {}}};
  auto* case_stmt = f.arena.Create<Stmt>();
  case_stmt->kind = StmtKind::kCase;
  case_stmt->condition = MakeInt(f.arena, 1);
  CaseItem ci;
  ci.is_default = true;
  ci.body = MakeAssign(f.arena, "data", MakeInt(f.arena, 3));
  case_stmt->case_items.push_back(ci);
  func->func_body_stmts = {case_stmt};

  ValidateConstRefWriteProtection(func, f.diag);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PassByRefValidation, NonRefArgsInStaticFuncAccepted) {
  SimFixture f;

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "ok_func";
  func->is_static = true;
  func->is_automatic = false;
  func->func_args = {
      {Direction::kInput, false, false, false, {}, "a", nullptr, {}},
      {Direction::kOutput, false, false, false, {}, "b", nullptr, {}},
      {Direction::kInout, false, false, false, {}, "c", nullptr, {}},
  };

  ValidateRefLifetime(func, f.diag);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
