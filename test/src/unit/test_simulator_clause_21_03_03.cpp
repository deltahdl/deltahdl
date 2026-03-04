// §21.3.3: Formatting data to a string

#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"
#include "simulator/eval.h"

using namespace delta;
namespace {

// ============================================================================
// §21.3.3 — $sformatf
// ============================================================================
TEST(Section20, SformatfBasic) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$sformatf",
                           {MkStr(f.arena, "val=%d"), MakeInt(f.arena, 42)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  // $sformatf returns a string as a Logic4Vec; the width should be
  // text.size()*8. "val=42" is 6 chars = 48 bits.
  EXPECT_EQ(result.width, 48u);
}

}  // namespace
