// §8.23: Class scope resolution operator ::

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "parser/ast.h"
#include "simulation/class_object.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"
#include <gtest/gtest.h>
#include <string>

using namespace delta;

// =============================================================================
// Test fixture — provides arena, scheduler, sim context, and helpers to
// build class types and objects at the AST/runtime level.
// =============================================================================
struct ClassFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};
// Build a simple ClassTypeInfo and register it with the context.
static ClassTypeInfo *
MakeClassType(ClassFixture &f, std::string_view name,
              const std::vector<std::string_view> &props) {
  auto *info = f.arena.Create<ClassTypeInfo>();
  info->name = name;
  for (auto p : props) {
    info->properties.push_back({p, 32, false});
  }
  f.ctx.RegisterClassType(name, info);
  return info;
}

namespace {

// =============================================================================
// §8.23: Class scope resolution operator ::
// =============================================================================
TEST(ClassSim, ScopeResolutionStaticLookup) {
  ClassFixture f;
  auto *type = MakeClassType(f, "MyClass", {});
  type->static_properties["MAX_SIZE"] = MakeLogic4VecVal(f.arena, 32, 256);

  auto it = type->static_properties.find("MAX_SIZE");
  ASSERT_NE(it, type->static_properties.end());
  EXPECT_EQ(it->second.ToUint64(), 256u);
}

TEST(ClassSim, ScopeResolutionMethodLookup) {
  ClassFixture f;
  auto *type = MakeClassType(f, "Utils", {});
  auto *method = f.arena.Create<ModuleItem>();
  method->kind = ModuleItemKind::kFunctionDecl;
  method->name = "compute";
  method->is_static = true;
  type->methods["compute"] = method;

  auto *found = f.ctx.FindClassType("Utils");
  ASSERT_NE(found, nullptr);
  auto it = found->methods.find("compute");
  ASSERT_NE(it, found->methods.end());
  EXPECT_EQ(it->second->name, "compute");
}

} // namespace
