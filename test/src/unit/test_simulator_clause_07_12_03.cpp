#include "fixture_simulator.h"
#include "simulator/eval_array.h"

using namespace delta;

static void MakeDynArray(SimFixture& f, std::string_view name,
                         const std::vector<uint64_t>& vals) {
  auto* q = f.ctx.CreateQueue(name, 32);
  for (auto v : vals) {
    q->elements.push_back(MakeLogic4VecVal(f.arena, 32, v));
  }
  ArrayInfo info;
  info.is_dynamic = true;
  info.elem_width = 32;
  info.size = static_cast<uint32_t>(vals.size());
  f.ctx.RegisterArray(name, info);
}

namespace {

// §7.12.3: sum() returns sum of all elements.
TEST(ArrayReduction, SumAllElements) {
  SimFixture f;
  MakeDynArray(f, "arr", {10, 20, 30, 40});
  Logic4Vec out;
  bool ok = TryEvalArrayProperty("arr", "sum", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 100u);
}

// §7.12.3: product() returns product of all elements.
TEST(ArrayReduction, ProductAllElements) {
  SimFixture f;
  MakeDynArray(f, "arr", {2, 3, 5});
  Logic4Vec out;
  bool ok = TryEvalArrayProperty("arr", "product", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 30u);
}

// §7.12.3: and() returns bitwise AND of all elements.
TEST(ArrayReduction, AndAllElements) {
  SimFixture f;
  MakeDynArray(f, "arr", {0xFF, 0x0F, 0x03});
  Logic4Vec out;
  bool ok = TryEvalArrayProperty("arr", "and", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0x03u);
}

// §7.12.3: or() returns bitwise OR of all elements.
TEST(ArrayReduction, OrAllElements) {
  SimFixture f;
  MakeDynArray(f, "arr", {0x01, 0x02, 0x04});
  Logic4Vec out;
  bool ok = TryEvalArrayProperty("arr", "or", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0x07u);
}

// §7.12.3: xor() returns bitwise XOR of all elements.
TEST(ArrayReduction, XorAllElements) {
  SimFixture f;
  MakeDynArray(f, "arr", {0x0F, 0xFF, 0xF0});
  Logic4Vec out;
  bool ok = TryEvalArrayProperty("arr", "xor", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0x00u);
}

}  // namespace
