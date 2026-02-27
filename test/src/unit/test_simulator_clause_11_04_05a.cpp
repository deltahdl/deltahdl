// §11.4.5: Equality operators

#include <cstring>

#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"  // StructTypeInfo, StructFieldInfo

#include "fixture_simulator.h"
#include "builders_ast.h"

using namespace delta;

static Variable* MakeVar(SimFixture& f, std::string_view name,
                         uint32_t width, uint64_t val) {
  auto* var = f.ctx.CreateVariable(name, width);
  var->value = MakeLogic4VecVal(f.arena, width, val);
  return var;
}

static Variable* MakeSignedVarAdv(SimFixture& f, std::string_view name,
                                  uint32_t width, uint64_t val) {
  auto* var = f.ctx.CreateVariable(name, width);
  var->value = MakeLogic4VecVal(f.arena, width, val);
  var->is_signed = true;
  return var;
}
namespace {

TEST(EvalAdv, PackedStructEqualitySameValue) {
  SimFixture f;
  // Two 16-bit packed struct vars with same value → == is 1.
  StructTypeInfo sinfo;
  sinfo.type_name = "my_struct";
  sinfo.total_width = 16;
  sinfo.is_packed = true;
  sinfo.fields.push_back({"a", 8, 8, DataTypeKind::kLogic});
  sinfo.fields.push_back({"b", 0, 8, DataTypeKind::kLogic});
  f.ctx.RegisterStructType("my_struct", sinfo);
  MakeVar(f, "s1", 16, 0xABCD);
  MakeVar(f, "s2", 16, 0xABCD);
  f.ctx.SetVariableStructType("s1", "my_struct");
  f.ctx.SetVariableStructType("s2", "my_struct");
  auto* expr = MakeBinary(f.arena, TokenKind::kEqEq, MakeId(f.arena, "s1"),
                          MakeId(f.arena, "s2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalAdv, PackedStructEqualityDiffValue) {
  SimFixture f;
  // Two 16-bit packed struct vars with different values → == is 0.
  StructTypeInfo sinfo;
  sinfo.type_name = "my_struct";
  sinfo.total_width = 16;
  sinfo.is_packed = true;
  sinfo.fields.push_back({"a", 8, 8, DataTypeKind::kLogic});
  sinfo.fields.push_back({"b", 0, 8, DataTypeKind::kLogic});
  f.ctx.RegisterStructType("my_struct", sinfo);
  MakeVar(f, "s3", 16, 0xABCD);
  MakeVar(f, "s4", 16, 0x1234);
  f.ctx.SetVariableStructType("s3", "my_struct");
  f.ctx.SetVariableStructType("s4", "my_struct");
  auto* expr = MakeBinary(f.arena, TokenKind::kEqEq, MakeId(f.arena, "s3"),
                          MakeId(f.arena, "s4"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalAdv, PackedStructInequality) {
  SimFixture f;
  StructTypeInfo sinfo;
  sinfo.type_name = "my_struct";
  sinfo.total_width = 16;
  sinfo.is_packed = true;
  sinfo.fields.push_back({"a", 8, 8, DataTypeKind::kLogic});
  sinfo.fields.push_back({"b", 0, 8, DataTypeKind::kLogic});
  f.ctx.RegisterStructType("my_struct", sinfo);
  MakeVar(f, "s5", 16, 0xABCD);
  MakeVar(f, "s6", 16, 0x1234);
  f.ctx.SetVariableStructType("s5", "my_struct");
  f.ctx.SetVariableStructType("s6", "my_struct");
  auto* expr = MakeBinary(f.arena, TokenKind::kBangEq, MakeId(f.arena, "s5"),
                          MakeId(f.arena, "s6"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalAdv, SignedEqNeg) {
  SimFixture f;
  MakeSignedVarAdv(f, "sa", 8, 0xFF);
  MakeSignedVarAdv(f, "sb", 8, 0xFF);
  auto* expr = MakeBinary(f.arena, TokenKind::kEqEq, MakeId(f.arena, "sa"),
                          MakeId(f.arena, "sb"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

}  // namespace
