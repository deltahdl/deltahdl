#include <gtest/gtest.h>

#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

std::vector<VpiHandle> Collect(VpiContext& ctx, VpiHandle iterator) {
  std::vector<VpiHandle> objects;
  if (!iterator) return objects;
  while (VpiHandle next = ctx.Scan(iterator)) objects.push_back(next);
  return objects;
}

TEST(MemoryModel, MemoryWordIterationReachesRegWords) {
  VpiContext ctx;

  VpiObject word0;
  word0.type = vpiReg;
  VpiObject left_range;
  left_range.type = vpiConstant;
  VpiObject word1;
  word1.type = vpiReg;

  VpiObject reg_array;
  reg_array.type = vpiRegArray;
  reg_array.children = {&word0, &left_range, &word1};

  std::vector<VpiHandle> words =
      Collect(ctx, ctx.Iterate(vpiMemoryWord, &reg_array));
  ASSERT_EQ(words.size(), 2u);
  EXPECT_EQ(words[0], &word0);
  EXPECT_EQ(words[1], &word1);
  EXPECT_EQ(words[0]->type, vpiReg);
  EXPECT_EQ(words[1]->type, vpiReg);
}

TEST(MemoryModel, MemoryWordIterationNullWhenNoWords) {
  VpiContext ctx;

  VpiObject reg_array;
  reg_array.type = vpiRegArray;
  EXPECT_EQ(ctx.Iterate(vpiMemoryWord, &reg_array), nullptr);
}

TEST(MemoryModel, MemoryWordIterationGatedToRegArray) {
  VpiContext ctx;

  VpiObject word;
  word.type = vpiReg;
  VpiObject not_an_array;
  not_an_array.type = vpiModule;
  not_an_array.children = {&word};

  EXPECT_EQ(ctx.Iterate(vpiMemoryWord, &not_an_array), nullptr);
}

TEST(MemoryPublic, MemoryIterationReturnsRegArrayObjects) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject word;
  word.type = vpiReg;
  VpiObject memory;
  memory.type = vpiRegArray;
  memory.children = {&word};
  VpiObject plain;
  plain.type = vpiReg;

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&plain, &memory};

  vpiHandle it = vpi_iterate(vpiMemory, VpiHandleOf(&scope));
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), &memory);
  EXPECT_EQ(vpi_scan(it), nullptr);

  SetGlobalVpiContext(nullptr);
}

TEST(MemoryPublic, MemoryIterationIsNullWhenTheScopeHasNoArray) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject plain;
  plain.type = vpiReg;

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&plain};

  EXPECT_EQ(vpi_iterate(vpiMemory, VpiHandleOf(&scope)), nullptr);

  SetGlobalVpiContext(nullptr);
}

TEST(MemoryPublic, IsMemoryDistinguishesARegArrayFromAnyOtherArray) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject reg_word;
  reg_word.type = vpiReg;
  VpiObject memory;
  memory.type = vpiRegArray;
  memory.children = {&reg_word};
  EXPECT_EQ(vpi_get(vpiIsMemory, VpiHandleOf(&memory)), 1);

  VpiObject int_word;
  int_word.type = vpiIntVar;
  VpiObject int_array;
  int_array.type = vpiArrayVar;
  int_array.children = {&int_word};
  EXPECT_EQ(vpi_get(vpiIsMemory, VpiHandleOf(&int_array)), 0);

  VpiObject not_an_array;
  not_an_array.type = vpiReg;
  EXPECT_EQ(vpi_get(vpiIsMemory, VpiHandleOf(&not_an_array)), 0);

  SetGlobalVpiContext(nullptr);
}

class MemoriesOfARun : public VpiDesignRun {};

TEST_F(MemoriesOfARun, AMemoryWordReachesItsIndex) {
  Run("module top;\n"
      "  reg [7:0] mem [4:7];\n"
      "endmodule\n");
  vpiHandle it = vpi_iterate(vpiMemoryWord, By("top.mem"));
  ASSERT_NE(it, nullptr);
  vpi_scan(it);
  vpi_scan(it);
  vpiHandle word = vpi_scan(it);
  ASSERT_NE(word, nullptr);
  vpi_free_object(it);
  vpiHandle index = vpi_handle(vpiIndex, word);
  ASSERT_NE(index, nullptr);
  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(index, &value);
  EXPECT_EQ(value.value.integer, 6);
}

}  // namespace
}  // namespace delta
