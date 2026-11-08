#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

struct AssertionKind {
  int type;
  const char* label;
};

constexpr AssertionKind kAssertionKinds[] = {
    {vpiSequenceInst, "sequence instance"},
    {vpiAssert, "assert"},
    {vpiAssume, "assume"},
    {vpiCover, "cover"},
    {vpiRestrict, "restrict"},
    {vpiPropertyInst, "property instance"},
    {vpiImmediateAssert, "immediate assert"},
    {vpiImmediateAssume, "immediate assume"},
    {vpiImmediateCover, "immediate cover"},
};

class AssertionStaticInformationItems : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

TEST_F(AssertionStaticInformationItems, EveryListedAssertionTypeReportsItself) {
  for (const AssertionKind& kind : kAssertionKinds) {
    VpiObject assertion;
    assertion.type = kind.type;

    EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&assertion)), kind.type)
        << kind.label;
    EXPECT_NE(vpi_get(vpiType, VpiHandleOf(&assertion)), vpiAssertion)
        << kind.label;
  }
}

TEST_F(AssertionStaticInformationItems, NameInstanceAndModuleDefinition) {
  VpiObject first_instance;
  first_instance.type = vpiModule;
  first_instance.name = "u1";
  first_instance.def_name = "handshake";
  VpiObject in_first;
  in_first.type = vpiAssert;
  in_first.name = "handshake_p";
  in_first.parent = &first_instance;
  first_instance.children = {&in_first};

  VpiObject second_instance;
  second_instance.type = vpiModule;
  second_instance.name = "u2";
  second_instance.def_name = "handshake";
  VpiObject in_second;
  in_second.type = vpiAssert;
  in_second.name = "handshake_p";
  in_second.parent = &second_instance;
  second_instance.children = {&in_second};

  EXPECT_STREQ(vpi_get_str(vpiName, VpiHandleOf(&in_first)), "handshake_p");
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiInstance, VpiHandleOf(&in_first))),
            &first_instance);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiInstance, VpiHandleOf(&in_second))),
            &second_instance);
  EXPECT_STREQ(
      vpi_get_str(vpiDefName, vpi_handle(vpiInstance, VpiHandleOf(&in_first))),
      "handshake");
  EXPECT_STREQ(
      vpi_get_str(vpiDefName, vpi_handle(vpiInstance, VpiHandleOf(&in_second))),
      "handshake");
}

TEST_F(AssertionStaticInformationItems, SourceInformationIsFileLineAndColumn) {
  VpiObject first;
  first.type = vpiAssert;
  first.file = "handshake.sv";
  first.start_line = 12;
  first.column = 5;
  first.end_line = 12;
  first.end_column = 30;

  VpiObject second;
  second.type = vpiCover;
  second.file = "handshake.sv";
  second.start_line = 12;
  second.column = 40;

  EXPECT_STREQ(vpi_get_str(vpiFile, VpiHandleOf(&first)), "handshake.sv");
  EXPECT_EQ(vpi_get(vpiStartLine, VpiHandleOf(&first)), 12);
  EXPECT_EQ(vpi_get(vpiColumn, VpiHandleOf(&first)), 5);
  EXPECT_EQ(vpi_get(vpiEndLine, VpiHandleOf(&first)), 12);
  EXPECT_EQ(vpi_get(vpiEndColumn, VpiHandleOf(&first)), 30);

  EXPECT_EQ(vpi_get(vpiStartLine, VpiHandleOf(&second)),
            vpi_get(vpiStartLine, VpiHandleOf(&first)));
  EXPECT_NE(vpi_get(vpiColumn, VpiHandleOf(&second)),
            vpi_get(vpiColumn, VpiHandleOf(&first)));
}

TEST_F(AssertionStaticInformationItems, TheClockingBlockGoverningTheAssertion) {
  VpiObject clocking;
  clocking.type = vpiClockingBlock;
  clocking.name = "cb";
  VpiObject clocked;
  clocked.type = vpiAssert;
  clocked.children = {&clocking};

  VpiObject unclocked;
  unclocked.type = vpiAssert;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiClockingBlock, VpiHandleOf(&clocked))),
            &clocking);
  EXPECT_EQ(vpi_handle(vpiClockingBlock, VpiHandleOf(&unclocked)), nullptr);
}

TEST_F(AssertionStaticInformationItems, TheClockingExpressionOfTheAssertion) {
  VpiObject event;
  event.type = vpiEventControl;
  VpiObject spec;
  spec.type = vpiPropertySpec;
  spec.children = {&event};

  VpiObject inner_event;
  inner_event.type = vpiEventControl;
  VpiObject clocked_property;
  clocked_property.type = vpiClockedProp;
  clocked_property.children = {&inner_event};

  VpiObject unclocked_spec;
  unclocked_spec.type = vpiPropertySpec;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiClockingEvent, VpiHandleOf(&spec))),
            &event);
  EXPECT_EQ(
      VpiObjectOf(vpi_handle(vpiClockingEvent, VpiHandleOf(&clocked_property))),
      &inner_event);
  EXPECT_EQ(vpi_handle(vpiClockingEvent, VpiHandleOf(&unclocked_spec)),
            nullptr);
}

}  // namespace
}  // namespace delta
