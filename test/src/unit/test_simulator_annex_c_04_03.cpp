#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"

// Annex C.4.3: VPI definitions.
//
// C.4.3 lists the object, relationship and property definitions deprecated to
// correct and improve VPI, "some ... inherited from IEEE Std 1364 (see 36.12.1)
// and some ... changed or removed to maintain consistency with related
// improvements". What it states of its own is where each still stands:
//
//   1) vpiMemory "no longer represents a VPI object type, except under certain
//      backwards compatibility modes (see 36.12.1)", and is still a
//      relationship (§37.20 detail 1);
//   2) vpiMemoryWord the same, its elements now being vpiLogicVar (vpiReg);
//   3) the vpiArray property "now has only limited use in IEEE Std 1364
//      backwards compatibility modes when vpiIntegerVar, vpiTimeVar, and
//      vpiRealVar could represent arrays", vpiArrayMember having replaced it;
//   4) vpiValid is inconsistent with its purpose and validity "is implicit in
//      their existence" (§38.36.1);
//   5) vpiInterfaceDecl "has been made equivalent to vpiVirtualInterfaceVar"
//      (§37.32 detail 11).
//
// Item 5 is a definition in simulator/sv_vpi_user.h and Annex M's tests read
// it; items 4 and the relationships of 1 and 2 are §38.36.1's and §37.20's.
// The backwards compatibility modes items 1 through 3 keep the old definitions
// under are §36.12.1 Table 36-10 rows 1 through 4, and this file observes
// vpi_get() answering under them: a mode selected as the run's default
// (§36.12.2.2) governs the plain entry point, and the variants §36.12.2.1
// renames an application's calls to carry their own version. Every variant
// forwarded to the current routine, so no mode had a memory object, an
// integer array was a vpiRegArray under every version, and vpiArray was the
// unknown property under the IEEE 1364 modes it is defined for.

// The compile-based variants, declared as vpi_compatibility.cpp defines them
// so that one translation unit can ask each version without selecting one
// before the headers, which admits a single version per unit.
PLI_INT32 vpi_get_1364v1995(PLI_INT32 property, vpiHandle obj);
PLI_INT32 vpi_get_1364v2001(PLI_INT32 property, vpiHandle obj);
PLI_INT32 vpi_get_1364v2005(PLI_INT32 property, vpiHandle obj);

namespace delta {
namespace {

class VpiDeprecatedDefinitions : public ::testing::Test {
 protected:
  void SetUp() override {
    SetGlobalVpiContext(&ctx_);
    word_.type = vpiReg;
    word_.parent = &memory_;
    memory_.type = vpiRegArray;
    memory_.children = {&word_};
    integer_word_.type = vpiIntegerVar;
    integer_word_.parent = &integer_array_;
    integer_array_.type = vpiRegArray;
    integer_array_.children = {&integer_word_};
    time_word_.type = vpiTimeVar;
    time_array_.type = vpiRegArray;
    time_array_.children = {&time_word_};
    real_word_.type = vpiRealVar;
    real_array_.type = vpiRegArray;
    real_array_.children = {&real_word_};
    integer_.type = vpiIntegerVar;
    module_.type = vpiModule;
    module_.children = {&memory_, &integer_array_, &time_array_, &real_array_,
                        &integer_};
    memory_.parent = &module_;
    integer_array_.parent = &module_;
    time_array_.parent = &module_;
    real_array_.parent = &module_;
    integer_.parent = &module_;
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext ctx_;
  VpiObject module_;
  VpiObject memory_;
  VpiObject word_;
  VpiObject integer_array_;
  VpiObject integer_word_;
  VpiObject time_array_;
  VpiObject time_word_;
  VpiObject real_array_;
  VpiObject real_word_;
  VpiObject integer_;
};

// Items 1 and 2 with Table 36-10 rows 1 and 2, Y for IEEE Std 1364-1995: under
// that mode an unpacked unidimensional reg array is a vpiMemory object and its
// element a vpiMemoryWord object, as §36.12.1 detail 1 has them "exclusively
// characterized".
TEST_F(VpiDeprecatedDefinitions, MemoryAndItsWordAreObjectsUnderThe1995Mode) {
  ASSERT_TRUE(ctx_.SetDefaultCompatibilityMode(vpiMode1364v1995));
  EXPECT_EQ(vpi_get(vpiType, &memory_), vpiMemory);
  EXPECT_EQ(vpi_get(vpiType, &word_), vpiMemoryWord);
  EXPECT_EQ(vpi_get_1364v1995(vpiType, &memory_), vpiMemory);
}

// Rows 1 and 2, D for IEEE Std 1364-2001: the objects are "present, but use
// discouraged", so an application compiled for that version still meets them.
TEST_F(VpiDeprecatedDefinitions, MemoryAndItsWordAreObjectsUnderThe2001Mode) {
  EXPECT_EQ(vpi_get_1364v2001(vpiType, &memory_), vpiMemory);
  EXPECT_EQ(vpi_get_1364v2001(vpiType, &word_), vpiMemoryWord);
}

// Rows 1 and 2, N from IEEE Std 1364-2005 on: the memory is the vpiRegArray
// that "replaced" the object type and its word the vpiReg, in that mode and in
// this standard's own behavior alike.
TEST_F(VpiDeprecatedDefinitions, MemoryIsAnArrayOfRegsFrom2005On) {
  EXPECT_EQ(vpi_get_1364v2005(vpiType, &memory_), vpiRegArray);
  EXPECT_EQ(vpi_get_1364v2005(vpiType, &word_), vpiReg);
  EXPECT_EQ(vpi_get(vpiType, &memory_), vpiRegArray);
  EXPECT_EQ(vpi_get(vpiType, &word_), vpiReg);
  ASSERT_TRUE(ctx_.SetDefaultCompatibilityMode(vpiMode1800v2009));
  EXPECT_EQ(vpi_get(vpiType, &memory_), vpiRegArray);
  EXPECT_EQ(vpi_get(vpiType, &word_), vpiReg);
}

// Row 1 has "unpacked unidimensional reg arrays" as the memories; an array of
// two unpacked dimensions is the vpiRegArray IEEE Std 1364-2001 introduced for
// it under every mode.
TEST_F(VpiDeprecatedDefinitions, AMultidimensionalRegArrayIsNoMemoryObject) {
  memory_.array_dim_indices = {{0, 1}, {0, 1}};
  ASSERT_TRUE(ctx_.SetDefaultCompatibilityMode(vpiMode1364v1995));
  EXPECT_EQ(vpi_get(vpiType, &memory_), vpiRegArray);
}

// A reg that is no element of a memory, one declared in the module, is a
// vpiReg under the 1995 mode as under this standard, and the other objects of
// the design keep their kinds.
TEST_F(VpiDeprecatedDefinitions, ARegOutsideAMemoryIsARegUnderThe1995Mode) {
  VpiObject reg;
  reg.type = vpiReg;
  reg.parent = &module_;
  VpiObject stray;
  stray.type = vpiReg;
  ASSERT_TRUE(ctx_.SetDefaultCompatibilityMode(vpiMode1364v1995));
  EXPECT_EQ(vpi_get(vpiType, &reg), vpiReg);
  EXPECT_EQ(vpi_get(vpiType, &stray), vpiReg);
  EXPECT_EQ(vpi_get(vpiType, &module_), vpiModule);
}

// Item 3 with rows 3 and 4, Y for every IEEE 1364 standard: under such a mode
// an unpacked array of integer or time variables is a vpiIntegerVar or
// vpiTimeVar object whose vpiArray property "returned TRUE when they were
// arrays", and the single variable of the kind answers FALSE.
TEST_F(VpiDeprecatedDefinitions,
       IntegerAndTimeArraysAreVariablesWithVpiArrayUnderThe1364Modes) {
  ASSERT_TRUE(ctx_.SetDefaultCompatibilityMode(vpiMode1364v1995));
  EXPECT_EQ(vpi_get(vpiType, &integer_array_), vpiIntegerVar);
  EXPECT_EQ(vpi_get(vpiArray, &integer_array_), 1);
  EXPECT_EQ(vpi_get(vpiType, &time_array_), vpiTimeVar);
  EXPECT_EQ(vpi_get(vpiArray, &time_array_), 1);
  EXPECT_EQ(vpi_get(vpiType, &integer_), vpiIntegerVar);
  EXPECT_EQ(vpi_get(vpiArray, &integer_), 0);
  EXPECT_EQ(vpi_get_1364v2005(vpiType, &integer_array_), vpiIntegerVar);
  EXPECT_EQ(vpi_get_1364v2005(vpiArray, &integer_array_), 1);
}

// Row 4, N for IEEE Std 1364-1995 and Y for 1364-2001 and 1364-2005: an
// unpacked array of reals is a vpiRealVar with vpiArray TRUE under the two
// later modes and the array object it is here under the first.
TEST_F(VpiDeprecatedDefinitions, ARealArrayIsARealVarFrom2001To2005) {
  EXPECT_EQ(vpi_get_1364v2001(vpiType, &real_array_), vpiRealVar);
  EXPECT_EQ(vpi_get_1364v2001(vpiArray, &real_array_), 1);
  EXPECT_EQ(vpi_get_1364v2005(vpiType, &real_array_), vpiRealVar);
  EXPECT_EQ(vpi_get_1364v1995(vpiType, &real_array_), vpiRegArray);
  EXPECT_EQ(vpi_get_1364v1995(vpiArray, &real_array_), 0);
}

// Item 3: vpiArray "indicated when vpiReg types represented elements of
// vpiRegArrays", so under the 2005 mode, where a memory's word is a vpiReg,
// the word answers TRUE and a reg that is no element answers FALSE.
TEST_F(VpiDeprecatedDefinitions, ARegElementOfAnArrayReportsVpiArrayUnder2005) {
  VpiObject reg;
  reg.type = vpiReg;
  reg.parent = &module_;
  EXPECT_EQ(vpi_get_1364v2005(vpiArray, &word_), 1);
  EXPECT_EQ(vpi_get_1364v2005(vpiArray, &reg), 0);
}

// An array of a kind no IEEE 1364 standard read as a variable, int variables
// here, is an array object with vpiArray FALSE under every mode, as is one
// that holds nothing yet.
TEST_F(VpiDeprecatedDefinitions, AnArrayOfAnotherKindStaysAnArrayObject) {
  VpiObject int_word;
  int_word.type = vpiIntVar;
  VpiObject int_array;
  int_array.type = vpiRegArray;
  int_array.children = {&int_word};
  VpiObject empty_array;
  empty_array.type = vpiRegArray;
  ASSERT_TRUE(ctx_.SetDefaultCompatibilityMode(vpiMode1364v2001));
  EXPECT_EQ(vpi_get(vpiType, &int_array), vpiRegArray);
  EXPECT_EQ(vpi_get(vpiArray, &int_array), 0);
  EXPECT_EQ(vpi_get(vpiType, &empty_array), vpiRegArray);
}

// Item 3: in this standard "the vpiArrayMember property is now used, thus
// replacing the original use of vpiArray", so outside the IEEE 1364 modes
// vpiArray is no property of an array or its element and an integer array is
// the vpiRegArray (vpiArrayVar) of §37.17, under the native behavior and an
// IEEE 1800 mode alike.
TEST_F(VpiDeprecatedDefinitions, VpiArrayIsNoPropertyOfThisStandard) {
  EXPECT_EQ(vpi_get(vpiType, &integer_array_), vpiRegArray);
  EXPECT_EQ(vpi_get(vpiArray, &integer_array_), 0);
  EXPECT_EQ(vpi_get(vpiArray, &word_), 0);
  ASSERT_TRUE(ctx_.SetDefaultCompatibilityMode(vpiMode1800v2009));
  EXPECT_EQ(vpi_get(vpiType, &integer_array_), vpiRegArray);
  EXPECT_EQ(vpi_get(vpiArray, &integer_array_), 0);
}

// The property that replaced it, §37.17 detail 2's and §37.16 detail 2's
// vpiArrayMember: TRUE for a variable that is an element of an array variable
// and for a net that is an element of an array net, FALSE for a variable
// declared on its own. The helpers answering it were reached by no property
// query, so every element answered FALSE.
TEST_F(VpiDeprecatedDefinitions, VpiArrayMemberTellsAnElementFromAVariable) {
  VpiObject net_array;
  net_array.type = vpiNetArray;
  VpiObject net;
  net.type = vpiNet;
  net.parent = &net_array;
  net_array.children = {&net};
  EXPECT_EQ(vpi_get(vpiArrayMember, &word_), 1);
  EXPECT_EQ(vpi_get(vpiArrayMember, &net), 1);
  EXPECT_EQ(vpi_get(vpiArrayMember, &integer_), 0);
}

// A mode changes the object type and vpiArray property and nothing else: the
// vpiIsMemory of §37.20 is answered as the current routine answers it under
// the 1995 mode, and a null handle gets the answer it gets under this standard.
TEST_F(VpiDeprecatedDefinitions, EveryOtherPropertyIsTheCurrentOne) {
  ASSERT_TRUE(ctx_.SetDefaultCompatibilityMode(vpiMode1364v1995));
  EXPECT_EQ(vpi_get(vpiIsMemory, &memory_), 1);
  EXPECT_EQ(vpi_get(vpiType, nullptr), 0);
}

// §37.3.6: asking for a property of a protected object other than vpiType is
// an error the current routine records and answers with vpiUndefined, and a
// mode keeps that answer rather than reading the object the error refused.
TEST_F(VpiDeprecatedDefinitions, AnErrorTheCurrentRoutineRecordsIsKept) {
  integer_array_.is_protected = true;
  ASSERT_TRUE(ctx_.SetDefaultCompatibilityMode(vpiMode1364v1995));
  EXPECT_EQ(vpi_get(vpiArray, &integer_array_), vpiUndefined);
  EXPECT_EQ(vpi_get(vpiType, &integer_array_), vpiIntegerVar);
}

}  // namespace
}  // namespace delta
