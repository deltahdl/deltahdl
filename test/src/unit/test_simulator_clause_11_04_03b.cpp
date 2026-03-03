// Non-LRM tests

#include <cstring>
#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/eval.h"
#include "simulator/sim_context.h"  // StructTypeInfo, StructFieldInfo

using namespace delta;

namespace {

TEST(EvalAdv, UnsignedDivUnchanged) {
  SimFixture f;
  auto* a = MakeVar(f, "ud", 8, 0xF9);
  (void)a;
  auto* b = MakeVar(f, "ue", 8, 2);
  (void)b;
  auto* expr = MakeBinary(f.arena, TokenKind::kSlash, MakeId(f.arena, "ud"),
                          MakeId(f.arena, "ue"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 124u);
}

}  // namespace
