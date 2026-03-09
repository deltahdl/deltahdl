#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "simulator/eval_array.h"

using namespace delta;

namespace {

TEST(ArrayReduction, SumAllElements) {
  SimFixture f;
  MakeDynArray(f, "arr", {10, 20, 30, 40});
  Logic4Vec out;
  bool ok = TryEvalArrayProperty("arr", "sum", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 100u);
}

TEST(ArrayReduction, ProductAllElements) {
  SimFixture f;
  MakeDynArray(f, "arr", {2, 3, 5});
  Logic4Vec out;
  bool ok = TryEvalArrayProperty("arr", "product", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 30u);
}

TEST(ArrayReduction, AndAllElements) {
  SimFixture f;
  MakeDynArray(f, "arr", {0xFF, 0x0F, 0x03});
  Logic4Vec out;
  bool ok = TryEvalArrayProperty("arr", "and", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0x03u);
}

TEST(ArrayReduction, OrAllElements) {
  SimFixture f;
  MakeDynArray(f, "arr", {0x01, 0x02, 0x04});
  Logic4Vec out;
  bool ok = TryEvalArrayProperty("arr", "or", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0x07u);
}

TEST(ArrayReduction, XorAllElements) {
  SimFixture f;
  MakeDynArray(f, "arr", {0x0F, 0xFF, 0xF0});
  Logic4Vec out;
  bool ok = TryEvalArrayProperty("arr", "xor", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0x00u);
}

}  // namespace
