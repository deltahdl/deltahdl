// §13.5.2: Pass by reference


#include "parser/ast.h"
#include "simulator/eval.h"

#include "fixture_simulator.h"

using namespace delta;

// ============================================================================
// Test fixture
// ============================================================================
namespace {

// ============================================================================
// A4: §6.21 — ValidateRefLifetime
// ============================================================================
// A static function with ref arg should produce a diagnostic error.
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

// An automatic function with ref arg should be accepted.
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

}  // namespace
