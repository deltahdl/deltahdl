#include <gtest/gtest.h>

#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.20 Memory: the VPI object model for a memory. Detail 1 is the clause's
// only own normative statement - the legacy vpiMemory and vpiMemoryWord objects
// have been generalized to arrays of variables and, for backwards
// compatibility, behave as methods returning vpiRegArray and vpiReg objects
// respectively. The vpiMemory iteration's item type (vpiRegArray) is owned by
// §37.10, and the reg/reg-array object definitions, ranges, parent edge, and
// access-by-index are owned by §37.17 and §38.19 (the cited dependencies). The
// piece §37.20 owns and is exercised here is the vpiMemoryWord relation: a reg
// array's words are reached as reg (vpiReg) objects.

// Walk an iterator to completion, collecting every object it yields in order.
std::vector<VpiHandle> Collect(VpiContext& ctx, VpiHandle iterator) {
  std::vector<VpiHandle> objects;
  if (!iterator) return objects;
  while (VpiHandle next = ctx.Scan(iterator)) objects.push_back(next);
  return objects;
}

// Detail 1: iterating vpiMemoryWord over a reg array reaches its reg word
// objects (vpiReg), in order, and skips any child that is not a reg word (for
// instance a range expression carried by the same reg array).
TEST(MemoryModel, MemoryWordIterationReachesRegWords) {
  VpiContext ctx;

  VpiObject word0;
  word0.type = vpiReg;
  VpiObject left_range;  // not a word: a vpiLeftRange expr, must be skipped
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

// Detail 1: a reg array with no reg word children yields nothing, so the
// vpiMemoryWord iterator is NULL.
TEST(MemoryModel, MemoryWordIterationNullWhenNoWords) {
  VpiContext ctx;

  VpiObject reg_array;
  reg_array.type = vpiRegArray;
  EXPECT_EQ(ctx.Iterate(vpiMemoryWord, &reg_array), nullptr);
}

// Detail 1 (boundary): the vpiMemoryWord relation is special only for a reg
// array (an array-variable kind). An object that is not a reg array - even one
// that happens to carry reg children - exposes no vpiMemoryWord iteration, so
// the iterator is NULL.
TEST(MemoryModel, MemoryWordIterationGatedToRegArray) {
  VpiContext ctx;

  VpiObject word;
  word.type = vpiReg;
  VpiObject not_an_array;
  not_an_array.type = vpiModule;
  not_an_array.children = {&word};

  EXPECT_EQ(ctx.Iterate(vpiMemoryWord, &not_an_array), nullptr);
}

}  // namespace
}  // namespace delta
