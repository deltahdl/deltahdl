#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

extern "C" {
PLI_INT32 vpi_get_1364v1995(PLI_INT32 property, vpiHandle obj);
PLI_INT32 vpi_get_1364v2001(PLI_INT32 property, vpiHandle obj);
PLI_INT32 vpi_get_1364v2005(PLI_INT32 property, vpiHandle obj);
}

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

TEST_F(VpiDeprecatedDefinitions, MemoryAndItsWordAreObjectsUnderThe1995Mode) {
  ASSERT_TRUE(ctx_.SetDefaultCompatibilityMode(vpiMode1364v1995));
  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&memory_)), vpiMemory);
  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&word_)), vpiMemoryWord);
  EXPECT_EQ(vpi_get_1364v1995(vpiType, VpiHandleOf(&memory_)), vpiMemory);
}

TEST_F(VpiDeprecatedDefinitions, MemoryAndItsWordAreObjectsUnderThe2001Mode) {
  EXPECT_EQ(vpi_get_1364v2001(vpiType, VpiHandleOf(&memory_)), vpiMemory);
  EXPECT_EQ(vpi_get_1364v2001(vpiType, VpiHandleOf(&word_)), vpiMemoryWord);
}

TEST_F(VpiDeprecatedDefinitions, MemoryIsAnArrayOfRegsFrom2005On) {
  EXPECT_EQ(vpi_get_1364v2005(vpiType, VpiHandleOf(&memory_)), vpiRegArray);
  EXPECT_EQ(vpi_get_1364v2005(vpiType, VpiHandleOf(&word_)), vpiReg);
  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&memory_)), vpiRegArray);
  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&word_)), vpiReg);
  ASSERT_TRUE(ctx_.SetDefaultCompatibilityMode(vpiMode1800v2009));
  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&memory_)), vpiRegArray);
  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&word_)), vpiReg);
}

TEST_F(VpiDeprecatedDefinitions, AMultidimensionalRegArrayIsNoMemoryObject) {
  memory_.array_dim_indices = {{0, 1}, {0, 1}};
  ASSERT_TRUE(ctx_.SetDefaultCompatibilityMode(vpiMode1364v1995));
  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&memory_)), vpiRegArray);
}

TEST_F(VpiDeprecatedDefinitions, ARegOutsideAMemoryIsARegUnderThe1995Mode) {
  VpiObject reg;
  reg.type = vpiReg;
  reg.parent = &module_;
  VpiObject stray;
  stray.type = vpiReg;
  ASSERT_TRUE(ctx_.SetDefaultCompatibilityMode(vpiMode1364v1995));
  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&reg)), vpiReg);
  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&stray)), vpiReg);
  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&module_)), vpiModule);
}

TEST_F(VpiDeprecatedDefinitions,
       IntegerAndTimeArraysAreVariablesWithVpiArrayUnderThe1364Modes) {
  ASSERT_TRUE(ctx_.SetDefaultCompatibilityMode(vpiMode1364v1995));
  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&integer_array_)), vpiIntegerVar);
  EXPECT_EQ(vpi_get(vpiArray, VpiHandleOf(&integer_array_)), 1);
  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&time_array_)), vpiTimeVar);
  EXPECT_EQ(vpi_get(vpiArray, VpiHandleOf(&time_array_)), 1);
  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&integer_)), vpiIntegerVar);
  EXPECT_EQ(vpi_get(vpiArray, VpiHandleOf(&integer_)), 0);
  EXPECT_EQ(vpi_get_1364v2005(vpiType, VpiHandleOf(&integer_array_)),
            vpiIntegerVar);
  EXPECT_EQ(vpi_get_1364v2005(vpiArray, VpiHandleOf(&integer_array_)), 1);
}

TEST_F(VpiDeprecatedDefinitions, ARealArrayIsARealVarFrom2001To2005) {
  EXPECT_EQ(vpi_get_1364v2001(vpiType, VpiHandleOf(&real_array_)), vpiRealVar);
  EXPECT_EQ(vpi_get_1364v2001(vpiArray, VpiHandleOf(&real_array_)), 1);
  EXPECT_EQ(vpi_get_1364v2005(vpiType, VpiHandleOf(&real_array_)), vpiRealVar);
  EXPECT_EQ(vpi_get_1364v1995(vpiType, VpiHandleOf(&real_array_)), vpiRegArray);
  EXPECT_EQ(vpi_get_1364v1995(vpiArray, VpiHandleOf(&real_array_)), 0);
}

TEST_F(VpiDeprecatedDefinitions, ARegElementOfAnArrayReportsVpiArrayUnder2005) {
  VpiObject reg;
  reg.type = vpiReg;
  reg.parent = &module_;
  EXPECT_EQ(vpi_get_1364v2005(vpiArray, VpiHandleOf(&word_)), 1);
  EXPECT_EQ(vpi_get_1364v2005(vpiArray, VpiHandleOf(&reg)), 0);
}

TEST_F(VpiDeprecatedDefinitions, AnArrayOfAnotherKindStaysAnArrayObject) {
  VpiObject int_word;
  int_word.type = vpiIntVar;
  VpiObject int_array;
  int_array.type = vpiRegArray;
  int_array.children = {&int_word};
  VpiObject empty_array;
  empty_array.type = vpiRegArray;
  ASSERT_TRUE(ctx_.SetDefaultCompatibilityMode(vpiMode1364v2001));
  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&int_array)), vpiRegArray);
  EXPECT_EQ(vpi_get(vpiArray, VpiHandleOf(&int_array)), 0);
  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&empty_array)), vpiRegArray);
}

TEST_F(VpiDeprecatedDefinitions, VpiArrayIsNoPropertyOfThisStandard) {
  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&integer_array_)), vpiRegArray);
  EXPECT_EQ(vpi_get(vpiArray, VpiHandleOf(&integer_array_)), 0);
  EXPECT_EQ(vpi_get(vpiArray, VpiHandleOf(&word_)), 0);
  ASSERT_TRUE(ctx_.SetDefaultCompatibilityMode(vpiMode1800v2009));
  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&integer_array_)), vpiRegArray);
  EXPECT_EQ(vpi_get(vpiArray, VpiHandleOf(&integer_array_)), 0);
}

TEST_F(VpiDeprecatedDefinitions, VpiArrayMemberTellsAnElementFromAVariable) {
  VpiObject net_array;
  net_array.type = vpiNetArray;
  VpiObject net;
  net.type = vpiNet;
  net.parent = &net_array;
  net_array.children = {&net};
  EXPECT_EQ(vpi_get(vpiArrayMember, VpiHandleOf(&word_)), 1);
  EXPECT_EQ(vpi_get(vpiArrayMember, VpiHandleOf(&net)), 1);
  EXPECT_EQ(vpi_get(vpiArrayMember, VpiHandleOf(&integer_)), 0);
}

TEST_F(VpiDeprecatedDefinitions, EveryOtherPropertyIsTheCurrentOne) {
  ASSERT_TRUE(ctx_.SetDefaultCompatibilityMode(vpiMode1364v1995));
  EXPECT_EQ(vpi_get(vpiIsMemory, VpiHandleOf(&memory_)), 1);
  EXPECT_EQ(vpi_get(vpiType, nullptr), vpiUndefined);
}

TEST_F(VpiDeprecatedDefinitions, AnErrorTheCurrentRoutineRecordsIsKept) {
  integer_array_.is_protected = true;
  ASSERT_TRUE(ctx_.SetDefaultCompatibilityMode(vpiMode1364v1995));
  EXPECT_EQ(vpi_get(vpiArray, VpiHandleOf(&integer_array_)), vpiUndefined);
  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&integer_array_)), vpiIntegerVar);
}

}  // namespace
}  // namespace delta
