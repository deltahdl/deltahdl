// §21.2: Display system tasks

#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"
#include "simulation/eval.h"
#include "simulation/eval_array.h"
#include "simulation/sim_context.h"

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

TEST(FormatArg, StringFromAscii) {
  Arena arena;
  // 'A' = 0x41 = 65
  auto val = MakeLogic4VecVal(arena, 8, 65);
  EXPECT_EQ(FormatValueAsString(val), "A");
}

}  // namespace
