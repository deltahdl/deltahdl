#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class SystfNameRules : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

PLI_INT32 CountCall(PLI_BYTE8* user_data) {
  ++*reinterpret_cast<int*>(user_data);
  return 0;
}

vpiHandle RegisterCountingTask(const std::string& name, int* counter) {
  s_vpi_systf_data task = {};
  task.type = vpiSysTask;
  task.tfname = VpiText(name.c_str());
  task.calltf = CountCall;
  task.user_data = reinterpret_cast<PLI_BYTE8*>(counter);
  return vpi_register_systf(&task);
}

void RunCalls(const std::string& body, SimFixture& f) {
  auto* design = ElaborateSrc(
      "module t;\n  initial begin\n" + body + "  end\nendmodule\n", f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
}

int CallsOfARegisteredName(const std::string& name) {
  int calls = 0;
  EXPECT_NE(RegisterCountingTask(name, &calls), nullptr);
  SimFixture f;
  RunCalls("    " + name + ";\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  return calls;
}

TEST_F(SystfNameRules, ADigitAfterTheDollarIsRegisteredAndCalled) {
  EXPECT_EQ(CallsOfARegisteredName("$1abc"), 1);
}

TEST_F(SystfNameRules, AnUnderscoreAfterTheDollarIsRegisteredAndCalled) {
  EXPECT_EQ(CallsOfARegisteredName("$_x"), 1);
}

TEST_F(SystfNameRules, ADollarAfterTheDollarIsRegisteredAndCalled) {
  EXPECT_EQ(CallsOfARegisteredName("$$x"), 1);
}

TEST_F(SystfNameRules, ADollarLaterInTheNameIsRegisteredAndCalled) {
  EXPECT_EQ(CallsOfARegisteredName("$a$b"), 1);
}

TEST_F(SystfNameRules, AnEmptyNameIsRefused) {
  int calls = 0;
  EXPECT_EQ(RegisterCountingTask("", &calls), nullptr);
  EXPECT_TRUE(vpi_ctx_.RegisteredSystfs().empty());
}

TEST_F(SystfNameRules, ASpaceInTheNameIsRefused) {
  int calls = 0;
  EXPECT_EQ(RegisterCountingTask("$has space", &calls), nullptr);
  EXPECT_TRUE(vpi_ctx_.RegisteredSystfs().empty());
}

TEST_F(SystfNameRules, APeriodInTheNameIsRefused) {
  int calls = 0;
  EXPECT_EQ(RegisterCountingTask("$dot.name", &calls), nullptr);
  EXPECT_TRUE(vpi_ctx_.RegisteredSystfs().empty());
}

TEST_F(SystfNameRules, ANonAsciiByteIsRefusedWhereAnAsciiLetterIsAccepted) {
  int calls = 0;
  EXPECT_EQ(RegisterCountingTask("$\xE9", &calls), nullptr);
  EXPECT_NE(RegisterCountingTask("$e", &calls), nullptr);
  EXPECT_EQ(vpi_ctx_.RegisteredSystfs().size(), 1U);
}

TEST_F(SystfNameRules, NamesDifferingOnlyInCaseReachTheirOwnApplications) {
  int upper = 0;
  int lower = 0;
  ASSERT_NE(RegisterCountingTask("$Foo", &upper), nullptr);
  ASSERT_NE(RegisterCountingTask("$foo", &lower), nullptr);
  SimFixture f;
  RunCalls("    $Foo;\n    $foo;\n    $foo;\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(upper, 1);
  EXPECT_EQ(lower, 2);
}

TEST_F(SystfNameRules, LongNamesDifferingLateReachTheirOwnApplications) {
  const std::string kStem = "$" + std::string(300, 'a');
  const std::string kFirstName = kStem + "x";
  const std::string kSecondName = kStem + "y";
  int first = 0;
  int second = 0;
  ASSERT_NE(RegisterCountingTask(kFirstName, &first), nullptr);
  ASSERT_NE(RegisterCountingTask(kSecondName, &second), nullptr);
  SimFixture f;
  RunCalls("    " + kFirstName + ";\n    " + kSecondName + ";\n    " +
               kSecondName + ";\n",
           f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(first, 1);
  EXPECT_EQ(second, 2);
}

}  // namespace
}  // namespace delta
