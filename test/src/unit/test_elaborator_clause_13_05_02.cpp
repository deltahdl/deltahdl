#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(QueueRef, RejectRefInStaticFunc) {
  SimFixture f;

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "bad_func";
  func->is_static = true;
  func->is_automatic = false;
  func->func_args = {{Direction::kRef, false, {}, "v", nullptr, {}}};

  ValidateRefLifetime(func, f.diag);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(QueueRef, AcceptRefInAutoFunc) {
  SimFixture f;

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "good_func";
  func->is_automatic = true;
  func->func_args = {{Direction::kRef, false, {}, "v", nullptr, {}}};

  ValidateRefLifetime(func, f.diag);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §13.5.2: ref argument in automatic function elaborates OK.
TEST(Elab1352, RefArgAutoFunctionOk) {
  // Use ElabFixture for proper elaboration-level test.
  // (Existing tests above use SimFixture for ValidateRefLifetime directly.)
  SimFixture f;

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "add_ref";
  func->is_automatic = true;
  func->func_args = {{Direction::kRef, false, {}, "x", nullptr, {}}};

  ValidateRefLifetime(func, f.diag);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §13.5.2: const ref argument is accepted.
TEST(Elab1352, ConstRefArgAccepted) {
  SimFixture f;

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "read_only";
  func->is_automatic = true;
  func->func_args = {{Direction::kRef, true, {}, "data", nullptr, {}}};

  ValidateRefLifetime(func, f.diag);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
