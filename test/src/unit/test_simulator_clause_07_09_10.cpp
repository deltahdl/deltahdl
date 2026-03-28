#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

TEST(AssocMethods, AssocArgCopyByValue) {
  SimFixture f;
  auto* src = f.ctx.CreateAssocArray("actual", 32, true);
  src->str_data["key1"] = MakeLogic4VecVal(f.arena, 32, 100);
  src->str_data["key2"] = MakeLogic4VecVal(f.arena, 32, 200);

  auto* dst =
      f.ctx.CreateAssocArray("formal", src->elem_width, src->is_string_key);
  dst->str_data = src->str_data;
  dst->has_default = src->has_default;
  dst->default_value = src->default_value;
  dst->index_width = src->index_width;

  EXPECT_EQ(dst->str_data.size(), 2u);
  EXPECT_EQ(dst->str_data["key1"].ToUint64(), 100u);

  dst->str_data["key1"] = MakeLogic4VecVal(f.arena, 32, 999);
  EXPECT_EQ(src->str_data["key1"].ToUint64(), 100u);
}

TEST(AssocMethods, AssocArgCopiesDefault) {
  SimFixture f;
  auto* src = f.ctx.CreateAssocArray("actual", 32, false);
  src->has_default = true;
  src->default_value = MakeLogic4VecVal(f.arena, 32, 42);
  src->int_data[1] = MakeLogic4VecVal(f.arena, 32, 10);

  auto* dst =
      f.ctx.CreateAssocArray("formal", src->elem_width, src->is_string_key);
  dst->int_data = src->int_data;
  dst->has_default = src->has_default;
  dst->default_value = src->default_value;
  dst->index_width = src->index_width;

  EXPECT_TRUE(dst->has_default);
  EXPECT_EQ(dst->default_value.ToUint64(), 42u);
  EXPECT_EQ(dst->int_data.size(), 1u);
}

TEST(AssocMethods, AssocArgByValueEndToEnd) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  function automatic int read_first(int x[int]);\n"
      "    return x[1];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    aa[1] = 55;\n"
      "    aa[2] = 66;\n"
      "    result = read_first(aa);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 55u);
}

TEST(AssocMethods, AssocArgCallerUnchangedEndToEnd) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int dummy;\n"
      "  int result;\n"
      "  function automatic int mutate(int x[int]);\n"
      "    x[1] = 999;\n"
      "    return 0;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    aa[1] = 42;\n"
      "    dummy = mutate(aa);\n"
      "    result = aa[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

}  // namespace
