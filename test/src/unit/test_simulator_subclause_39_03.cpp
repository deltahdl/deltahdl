#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "simulator/dpi_runtime.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"
#include "simulator/vpi_assertion_cb.h"

namespace delta {
namespace {

// §39.3 "Static information" says what the subclause is for in one sentence:
// "This subclause defines how to obtain assertion handles and other static
// assertion information." The two halves are written out below it - §39.3.1 for
// the handle and §39.3.2 for the information reached through it - so what §39.3
// itself says is that the two go together, and that the second kind of thing is
// static. Static is the word that separates this subclause from §39.4's dynamic
// information: what is read here is a property of the assertion as it was
// written, so a run that attempts the assertion, fails it, and disables it
// leaves every one of these answers where it found them. These tests obtain a
// handle and read the static information through it, and then run the assertion
// through those dynamics and read it again.

// The static information this tool answers for an assertion, gathered the way
// an application would: from the handle alone.
struct StaticAssertionInfo {
  std::string name;
  int type = 0;
  vpiHandle instance = nullptr;
  std::string file;
  int line = 0;
};

StaticAssertionInfo ReadStaticInfo(vpiHandle assertion) {
  StaticAssertionInfo info;
  info.name = vpi_get_str(vpiName, assertion);
  info.type = vpi_get(vpiType, assertion);
  info.instance = vpi_handle(vpiInstance, assertion);
  info.file = vpi_get_str(vpiFile, assertion);
  info.line = vpi_get(vpiLineNo, assertion);
  return info;
}

class AssertionStaticInformation : public ::testing::Test {
 protected:
  void SetUp() override {
    SetGlobalVpiContext(&vpi_ctx_);
    SetGlobalAssertionApi(&api_);

    dut_.type = vpiModule;
    dut_.name = "dut";
    assertion_.type = vpiAssert;
    assertion_.name = "handshake_p";
    assertion_.file = "dut.sv";
    assertion_.line_no = 42;
    assertion_.parent = &dut_;
    dut_.children = {&assertion_};
  }
  void TearDown() override {
    SetGlobalAssertionApi(nullptr);
    SetGlobalVpiContext(nullptr);
  }

  VpiObject dut_;
  VpiObject assertion_;
  VpiContext vpi_ctx_;
  AssertionApi api_;
};

// §39.3, both halves in one: the handle comes from the assertion-class
// iteration of §39.3.1, and the static information of §39.3.2 - the assertion's
// name, its type, the instance it occurs in, and the file and line it was
// written on - is read through that handle and through nothing else.
TEST_F(AssertionStaticInformation,
       TheHandleIsWhatTheStaticInformationIsReadFrom) {
  vpiHandle it = vpi_iterate(vpiAssertion, &dut_);
  ASSERT_NE(it, nullptr);
  vpiHandle assertion = vpi_scan(it);
  ASSERT_EQ(assertion, &assertion_);
  ASSERT_EQ(vpi_scan(it), nullptr);

  StaticAssertionInfo info = ReadStaticInfo(assertion);
  EXPECT_EQ(info.name, "handshake_p");
  EXPECT_EQ(info.type, vpiAssert);
  EXPECT_EQ(info.instance, &dut_);
  EXPECT_EQ(info.file, "dut.sv");
  EXPECT_EQ(info.line, 42);
}

// §39.3: what this subclause obtains is static, which is what puts it on the
// other side of the line from §39.4's dynamic information. The assertion here
// is attempted twice, fails, and is then disabled by a control action - the
// dynamic side moves under it every time - and the name, type, instance, file
// and line it reports afterwards are the ones it reported before any of it.
TEST_F(AssertionStaticInformation, TheInformationDoesNotMoveWhileTheRunDoes) {
  StaticAssertionInfo before = ReadStaticInfo(&assertion_);

  api_.NoteAssertionAttemptStarted("handshake_p", 10);
  api_.NoteAssertionAttemptStarted("handshake_p", 20);
  AssertionAttemptInfo attempt;
  attempt.attempt_start_time = 10;
  attempt.fail_expr = "req && !ack";
  api_.DeliverAssertionEvent("handshake_p", cbAssertionFailure, 14, attempt);
  ASSERT_TRUE(api_.Control(vpiAssertionDisable, "handshake_p"));

  // The dynamic side did move: the assertion is no longer enabled.
  ASSERT_FALSE(api_.AssertionEnabled("handshake_p"));

  StaticAssertionInfo after = ReadStaticInfo(&assertion_);
  EXPECT_EQ(after.name, before.name);
  EXPECT_EQ(after.type, before.type);
  EXPECT_EQ(after.instance, before.instance);
  EXPECT_EQ(after.file, before.file);
  EXPECT_EQ(after.line, before.line);
}

}  // namespace
}  // namespace delta
