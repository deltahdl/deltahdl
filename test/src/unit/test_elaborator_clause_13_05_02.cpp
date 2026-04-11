#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(PassByRefValidation, RejectRefInStaticFunc) {
  SimFixture f;

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "bad_func";
  func->is_static = true;
  func->is_automatic = false;
  func->func_args = {{Direction::kRef, false, false, false, {}, "v", nullptr, {}}};

  ValidateRefLifetime(func, f.diag);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PassByRefValidation, AcceptRefInAutoFunc) {
  SimFixture f;

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "good_func";
  func->is_automatic = true;
  func->func_args = {{Direction::kRef, false, false, false, {}, "v", nullptr, {}}};

  ValidateRefLifetime(func, f.diag);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PassByRefValidation, RefArgAutoFunctionOk) {
  SimFixture f;

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "add_ref";
  func->is_automatic = true;
  func->func_args = {{Direction::kRef, false, false, false, {}, "x", nullptr, {}}};

  ValidateRefLifetime(func, f.diag);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PassByRefValidation, ConstRefArgAccepted) {
  SimFixture f;

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "read_only";
  func->is_automatic = true;
  func->func_args = {{Direction::kRef, true, false, false, {}, "data", nullptr, {}}};

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
  task->func_args = {{Direction::kRef, false, false, false, {}, "v", nullptr, {}}};

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
  func->func_args = {{Direction::kRef, true, false, false, {}, "data", nullptr, {}}};

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
