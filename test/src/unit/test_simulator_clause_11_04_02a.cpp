// §11.4.2: Increment and decrement operators

#include <cstring>

#include "parser/ast.h"
#include "simulator/eval.h"
#include "simulator/sim_context.h"  // StructTypeInfo, StructFieldInfo

#include "fixture_simulator.h"
#include "builders_ast.h"

using namespace delta;

static double AdvToDouble(const Logic4Vec& v) {
  double d = 0.0;
  uint64_t bits = v.ToUint64();
  std::memcpy(&d, &bits, sizeof(double));
  return d;
}

static Variable* MakeRealVarAdv(SimFixture& f, std::string_view name,
                                double val) {
  auto* var = f.ctx.CreateVariable(name, 64);
  uint64_t bits = 0;
  std::memcpy(&bits, &val, sizeof(double));
  var->value = MakeLogic4VecVal(f.arena, 64, bits);
  var->value.is_real = true;
  f.ctx.RegisterRealVariable(name);
  return var;
}
namespace {

TEST(EvalAdv, RealIncrementBy1Point0) {
  SimFixture f;
  // §11.4.2: ++real_var should increment by 1.0, not by integer 1.
  MakeRealVarAdv(f, "rv", 2.5);
  auto* inc = f.arena.Create<Expr>();
  inc->kind = ExprKind::kUnary;
  inc->op = TokenKind::kPlusPlus;
  inc->lhs = MakeId(f.arena, "rv");
  auto result = EvalExpr(inc, f.ctx, f.arena);
  EXPECT_TRUE(result.is_real);
  EXPECT_DOUBLE_EQ(AdvToDouble(result), 3.5);
}

}  // namespace
