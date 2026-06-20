#include "builders_ast.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

inline std::string DecodeAsciiBytes(const Logic4Vec& vec) {
  uint32_t nbytes = vec.width / 8;
  std::string out;
  for (uint32_t i = nbytes; i > 0; --i) {
    uint32_t byte_idx = i - 1;
    uint32_t word = (byte_idx * 8) / 64;
    uint32_t bit = (byte_idx * 8) % 64;
    if (word >= vec.nwords) continue;
    auto ch = static_cast<char>((vec.words[word].aval >> bit) & 0xFF);
    if (ch != 0) out += ch;
  }
  return out;
}

TEST(UtilitySystemTaskTest, Typename) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$typename", {MakeInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);

  EXPECT_EQ(DecodeAsciiBytes(result), "logic");
}

TEST(UtilitySystemTaskTest, TypenameDefaultSigningRemoved) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("y", 32);
  var->is_signed = true;
  var->is_4state = false;
  auto* expr = MakeSysCall(f.arena, "$typename", {MakeId(f.arena, "y")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(DecodeAsciiBytes(result), "int");
}

TEST(UtilitySystemTaskTest, TypenameVectorRangeIsUnsizedDecimal) {
  SimFixture f;
  f.ctx.CreateVariable("data", 8);
  auto* expr = MakeSysCall(f.arena, "$typename", {MakeId(f.arena, "data")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(DecodeAsciiBytes(result), "logic[7:0]");
}

TEST(UtilitySystemTaskTest, TypenameSingleBitLogic) {
  SimFixture f;
  f.ctx.CreateVariable("flag", 1);
  auto* expr = MakeSysCall(f.arena, "$typename", {MakeId(f.arena, "flag")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(DecodeAsciiBytes(result), "logic");
}

TEST(UtilitySystemTaskTest, TypenameSingleBitTwoState) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("b1", 1);
  var->is_4state = false;
  auto* expr = MakeSysCall(f.arena, "$typename", {MakeId(f.arena, "b1")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(DecodeAsciiBytes(result), "bit");
}

TEST(UtilitySystemTaskTest, TypenameTwoStateSignedNarrowVector) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("by", 8);
  var->is_4state = false;
  var->is_signed = true;
  auto* expr = MakeSysCall(f.arena, "$typename", {MakeId(f.arena, "by")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(DecodeAsciiBytes(result), "bit[7:0]");
}

TEST(UtilitySystemTaskTest, TypenameUnknownIdentifierFallback) {
  SimFixture f;
  auto* expr =
      MakeSysCall(f.arena, "$typename", {MakeId(f.arena, "no_such_var")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(DecodeAsciiBytes(result), "logic");
}

TEST(UtilitySystemTaskTest, TypenameNoArgsFallback) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$typename", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(DecodeAsciiBytes(result), "logic");
}

}  // namespace
