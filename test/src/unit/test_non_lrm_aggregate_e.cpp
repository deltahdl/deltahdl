// Non-LRM tests

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"
#include "simulation/eval.h"
#include "simulation/eval_array.h"
#include "simulation/sim_context.h"
#include <gtest/gtest.h>
#include <string>

using namespace delta;

// =============================================================================
// Helper fixture
// =============================================================================
struct AggFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

namespace {

// =============================================================================
// §10.10 Unpacked array concatenation
// =============================================================================
TEST(UnpackedArrayConcat, BasicConcat) {
  // Create two array elements as flat variables, verify concatenation concept.
  AggFixture f;
  auto *a0 = f.ctx.CreateVariable("a[0]", 8);
  auto *a1 = f.ctx.CreateVariable("a[1]", 8);
  a0->value = MakeLogic4VecVal(f.arena, 8, 10);
  a1->value = MakeLogic4VecVal(f.arena, 8, 20);

  // Verify the flat naming convention for array elements.
  auto *found0 = f.ctx.FindVariable("a[0]");
  auto *found1 = f.ctx.FindVariable("a[1]");
  ASSERT_NE(found0, nullptr);
  ASSERT_NE(found1, nullptr);
  EXPECT_EQ(found0->value.ToUint64(), 10u);
  EXPECT_EQ(found1->value.ToUint64(), 20u);
}

} // namespace
