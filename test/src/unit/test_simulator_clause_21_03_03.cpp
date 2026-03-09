#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"
#include "simulator/evaluation.h"

using namespace delta;
namespace {

TEST(Section20, SformatfBasic) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$sformatf",
                           {MkStr(f.arena, "val=%d"), MakeInt(f.arena, 42)});
  auto result = EvalExpr(expr, f.ctx, f.arena);

  EXPECT_EQ(result.width, 48u);
}

}
