#include <gtest/gtest.h>

#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §36.12 (VPI backwards compatibility features and limitations) summarizes, in
// Table 36-10, how the VPI data model differs across the standards. The column
// that binds a tool built to this standard is the last one - "2012 2017 2023" -
// and the rows are read with the table key: Y is a behavior present in that
// version, N one no longer present.
//
// The rows this simulator answers for structurally are the ones about arrays of
// variables. §37.17 detail 19 makes vpiReg and vpiRegArray the same kinds as
// vpiLogicVar and vpiArrayVar, and an unpacked array of any variable is a
// vpiRegArray object, which is what rows 1, 2, 5, 6 and 7 are about.
class VpiCompatibility : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  std::vector<vpiHandle> ScanAll(vpiHandle it) {
    std::vector<vpiHandle> seen;
    if (it == nullptr) return seen;
    while (vpiHandle h = vpi_scan(it)) seen.push_back(h);
    return seen;
  }

  VpiContext ctx_;
};

// Row 6 (Y): "vpiReg iterations on vpiRegArray include other objects." The
// detail says why - the array object represents an unpacked array of any
// variable, so "vpiReg iterations on these array objects can retrieve array
// elements that are of type vpiIntegerVar or vpiTimeVar for example, which is
// not expected in IEEE Std 1364-2001 and IEEE Std 1364-2005." The iteration
// matched a child's own type against vpiReg, so it retrieved the reg elements
// and walked past every element of another kind.
TEST_F(VpiCompatibility, ARegIterationOnAnArrayRetrievesElementsOfEveryKind) {
  VpiObject reg_word;
  reg_word.type = vpiReg;
  VpiObject integer_word;
  integer_word.type = vpiIntegerVar;
  VpiObject time_word;
  time_word.type = vpiTimeVar;

  VpiObject array;
  array.type = vpiRegArray;
  array.children = {&reg_word, &integer_word, &time_word};

  std::vector<vpiHandle> seen = ScanAll(vpi_iterate(vpiReg, &array));
  ASSERT_EQ(seen.size(), 3u);
  EXPECT_EQ(seen[0], &reg_word);
  EXPECT_EQ(seen[1], &integer_word);
  EXPECT_EQ(seen[2], &time_word);
}

// Row 6 scope: the row is about an iteration on an array object. A scope's own
// vpiReg iteration is the §37.12 one and keeps reporting the regs it declares,
// so an int var standing beside them is not swept up as one.
TEST_F(VpiCompatibility, ARegIterationOnAScopeIsUnaffected) {
  VpiObject reg;
  reg.type = vpiReg;
  VpiObject int_var;
  int_var.type = vpiIntegerVar;

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&reg, &int_var};

  std::vector<vpiHandle> seen = ScanAll(vpi_iterate(vpiReg, &scope));
  ASSERT_EQ(seen.size(), 1u);
  EXPECT_EQ(seen[0], &reg);
}

// Row 5 (Y): "vpiVariables iterations include vpiReg and vpiRegArray." In the
// IEEE 1364 standards both were excluded from that iteration; here they are
// among what it reaches.
TEST_F(VpiCompatibility, AVariablesIterationIncludesRegsAndRegArrays) {
  VpiObject reg;
  reg.type = vpiReg;
  VpiObject array;
  array.type = vpiRegArray;

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&reg, &array};

  std::vector<vpiHandle> seen = ScanAll(vpi_iterate(vpiVariables, &scope));
  ASSERT_EQ(seen.size(), 2u);
  EXPECT_EQ(seen[0], &reg);
  EXPECT_EQ(seen[1], &array);
}

// Row 7 (Y): "vpiRegArray iterations include variable array objects." The
// detail names the kinds - "this iteration includes arrays of vpiIntegerVar,
// vpiTimeVar, and vpiRealVar" - which are all vpiRegArray objects here, so one
// iteration reaches every array a scope declares whatever its elements are.
TEST_F(VpiCompatibility, ARegArrayIterationIncludesArraysOfEveryVariable) {
  VpiObject int_word;
  int_word.type = vpiIntegerVar;
  VpiObject int_array;
  int_array.type = vpiRegArray;
  int_array.children = {&int_word};

  VpiObject real_word;
  real_word.type = vpiRealVar;
  VpiObject real_array;
  real_array.type = vpiRegArray;
  real_array.children = {&real_word};

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&int_array, &real_array};

  std::vector<vpiHandle> seen = ScanAll(vpi_iterate(vpiRegArray, &scope));
  ASSERT_EQ(seen.size(), 2u);
  EXPECT_EQ(seen[0], &int_array);
  EXPECT_EQ(seen[1], &real_array);
}

// Rows 1 and 2 (N): vpiMemory and vpiMemoryWord no longer exist as objects.
// §37.20 detail 1 leaves them as the methods returning vpiRegArray and vpiReg,
// so each is a relation an application asks for and neither is a kind an object
// carries - a scope's memories come back as arrays and their words as regs.
TEST_F(VpiCompatibility, MemoryAndMemoryWordAreRelationsRatherThanObjects) {
  VpiObject word;
  word.type = vpiReg;
  VpiObject memory;
  memory.type = vpiRegArray;
  memory.children = {&word};

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&memory};

  std::vector<vpiHandle> memories = ScanAll(vpi_iterate(vpiMemory, &scope));
  ASSERT_EQ(memories.size(), 1u);
  EXPECT_EQ(memories[0], &memory);
  EXPECT_EQ(vpi_get(vpiType, memories[0]), vpiRegArray);

  std::vector<vpiHandle> words = ScanAll(vpi_iterate(vpiMemoryWord, &memory));
  ASSERT_EQ(words.size(), 1u);
  EXPECT_EQ(words[0], &word);
  EXPECT_EQ(vpi_get(vpiType, words[0]), vpiReg);
}

}  // namespace
}  // namespace delta
