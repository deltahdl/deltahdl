// §7.3.2: Tagged unions

#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/eval.h"
#include "simulator/eval_array.h"

using namespace delta;

namespace {

TEST(TaggedUnion, ChangeTag) {
  SimFixture f;
  f.ctx.CreateVariable("u", 32);
  f.ctx.SetVariableTag("u", "a");
  EXPECT_EQ(f.ctx.GetVariableTag("u"), "a");
  f.ctx.SetVariableTag("u", "b");
  EXPECT_EQ(f.ctx.GetVariableTag("u"), "b");
}

}  // namespace
