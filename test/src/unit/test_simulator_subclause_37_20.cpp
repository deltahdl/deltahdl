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

// -----------------------------------------------------------------------------
// The other half of detail 1, and the property beside it. vpiMemory and
// vpiMemoryWord "have been converted into methods that will return objects of
// type vpiRegArray and vpiReg, respectively". The word half was answered; the
// memory half was not, so vpi_iterate(vpiMemory, scope) looked for a child
// whose own type is the legacy vpiMemory kind - which no design builds - and
// reached none of a scope's memories. vpiIsMemory, drawn on the reg array
// beside it, was dispatched by nothing and answered FALSE for every one.
// -----------------------------------------------------------------------------

// Detail 1: the vpiMemory iteration returns objects of type vpiRegArray, so a
// scope's memories are the array variables it declares. A variable that is not
// an array is not one of them.
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

  vpiHandle it = vpi_iterate(vpiMemory, &scope);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(vpi_scan(it), &memory);
  EXPECT_EQ(vpi_scan(it), nullptr);

  SetGlobalVpiContext(nullptr);
}

// Detail 1: a scope declaring no array variable has no memory to reach, which
// §38.23 reports as no iterator.
TEST(MemoryPublic, MemoryIterationIsNullWhenTheScopeHasNoArray) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject plain;
  plain.type = vpiReg;

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&plain};

  EXPECT_EQ(vpi_iterate(vpiMemory, &scope), nullptr);

  SetGlobalVpiContext(nullptr);
}

// Figure (reg array -> is a memory): the array reports whether it is one.
// Detail 1 makes a memory's words regs, so an array of regs is a memory and an
// array of some other variable kind is an array variable that is not.
TEST(MemoryPublic, IsMemoryDistinguishesARegArrayFromAnyOtherArray) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject reg_word;
  reg_word.type = vpiReg;
  VpiObject memory;
  memory.type = vpiRegArray;
  memory.children = {&reg_word};
  EXPECT_EQ(vpi_get(vpiIsMemory, &memory), 1);

  VpiObject int_word;
  int_word.type = vpiIntVar;
  VpiObject int_array;
  int_array.type = vpiArrayVar;
  int_array.children = {&int_word};
  EXPECT_EQ(vpi_get(vpiIsMemory, &int_array), 0);

  VpiObject not_an_array;
  not_an_array.type = vpiReg;
  EXPECT_EQ(vpi_get(vpiIsMemory, &not_an_array), 0);

  SetGlobalVpiContext(nullptr);
}

}  // namespace
}  // namespace delta
