// §11.9: Tagged union expressions and member access

#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/eval.h"
#include "simulator/eval_array.h"

using namespace delta;

// =============================================================================
// Helper fixture
// =============================================================================
namespace {

// =============================================================================
// §11.9 Tagged union — tag tracking
// =============================================================================
TEST(TaggedUnion, SetAndGetTag) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("u", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0);

  f.ctx.SetVariableTag("u", "field_a");
  EXPECT_EQ(f.ctx.GetVariableTag("u"), "field_a");
}

TEST(TaggedUnion, TagDefaultEmpty) {
  SimFixture f;
  EXPECT_TRUE(f.ctx.GetVariableTag("nonexistent").empty());
}

TEST(TaggedUnion, ChangeTag) {
  SimFixture f;
  f.ctx.CreateVariable("u", 32);
  f.ctx.SetVariableTag("u", "a");
  EXPECT_EQ(f.ctx.GetVariableTag("u"), "a");
  f.ctx.SetVariableTag("u", "b");
  EXPECT_EQ(f.ctx.GetVariableTag("u"), "b");
}

}  // namespace
