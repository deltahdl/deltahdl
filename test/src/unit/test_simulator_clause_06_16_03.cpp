#include "builders_ast.h"
#include "fixture_string.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(StringMethods, Getc) {
  StringFixture f;
  f.CreateStringVar("s", "hello");
  auto* call = f.MakeMethodCall("s", "getc", {f.MakeIntLiteral(1)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), static_cast<uint64_t>('e'));
}

// §6.16.3: getc is declared as `function byte getc(int i)`, so a single
// character is a byte — the result must be exactly 8 bits wide.
TEST(StringMethods, GetcReturnsByteWidth) {
  StringFixture f;
  f.CreateStringVar("s", "hello");
  auto* call = f.MakeMethodCall("s", "getc", {f.MakeIntLiteral(1)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.width, 8u);
}

TEST(StringMethods, GetcOutOfBounds) {
  StringFixture f;
  f.CreateStringVar("s", "hi");
  auto* call = f.MakeMethodCall("s", "getc", {f.MakeIntLiteral(10)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// §6.16.3: the out-of-bounds guard is i >= str.len(), so an index equal to the
// length is itself out of bounds (valid indices run 0..len-1). Pin that exact
// boundary against an off-by-one in the production guard.
TEST(StringMethods, GetcIndexEqualsLength) {
  StringFixture f;
  f.CreateStringVar("s", "hi");
  auto* call = f.MakeMethodCall("s", "getc", {f.MakeIntLiteral(2)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(StringMethods, GetcNegativeIndex) {
  StringFixture f;
  f.CreateStringVar("s", "hi");
  auto* neg = f.MakeIntLiteral(-1);
  auto* call = f.MakeMethodCall("s", "getc", {neg});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(StringMethods, GetcFirstCharacter) {
  StringFixture f;
  f.CreateStringVar("s", "abc");
  auto* call = f.MakeMethodCall("s", "getc", {f.MakeIntLiteral(0)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), static_cast<uint64_t>('a'));
}

TEST(StringMethods, GetcLastCharacter) {
  StringFixture f;
  f.CreateStringVar("s", "abc");
  auto* call = f.MakeMethodCall("s", "getc", {f.MakeIntLiteral(2)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), static_cast<uint64_t>('c'));
}

TEST(StringMethods, GetcEmptyString) {
  StringFixture f;
  f.CreateStringVar("s", "");
  auto* call = f.MakeMethodCall("s", "getc", {f.MakeIntLiteral(0)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// §6.16.3: x = str.getc(j) is defined to be semantically equivalent to the
// indexed read x = str[j]. Drive both paths on the same string at an in-range
// position and confirm they produce the identical character code.
TEST(StringMethods, GetcEquivalentToIndexedRead) {
  StringFixture f;
  f.CreateStringVar("s", "world");

  auto* call = f.MakeMethodCall("s", "getc", {f.MakeIntLiteral(2)});
  auto via_getc = EvalExpr(call, f.ctx, f.arena);

  auto* index =
      MakeSelectExpr(f.arena, MakeId(f.arena, "s"), MakeInt(f.arena, 2));
  auto via_index = EvalExpr(index, f.ctx, f.arena);

  EXPECT_EQ(via_getc.ToUint64(), static_cast<uint64_t>('r'));
  EXPECT_EQ(via_getc.ToUint64(), via_index.ToUint64());
}

// §6.16.3: the equivalence holds at the out-of-bounds boundary too — getc(j)
// returns 0 for j >= len, and so does the indexed read str[j].
TEST(StringMethods, GetcEquivalentToIndexedReadOutOfBounds) {
  StringFixture f;
  f.CreateStringVar("s", "world");

  auto* call = f.MakeMethodCall("s", "getc", {f.MakeIntLiteral(5)});
  auto via_getc = EvalExpr(call, f.ctx, f.arena);

  auto* index =
      MakeSelectExpr(f.arena, MakeId(f.arena, "s"), MakeInt(f.arena, 5));
  auto via_index = EvalExpr(index, f.ctx, f.arena);

  EXPECT_EQ(via_getc.ToUint64(), 0u);
  EXPECT_EQ(via_getc.ToUint64(), via_index.ToUint64());
}

}  // namespace
