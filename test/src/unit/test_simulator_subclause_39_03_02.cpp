#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §39.3.2 "Obtaining static assertion information" lists what is static about
// an assertion, and the list is the whole of the subclause: the assertion name;
// the instance in which the assertion occurs; the module definition containing
// it; the assertion type, of which it names nine kinds; the assertion source
// information, "the file, line, and column where the assertion is defined"; and
// the assertion clocking block/expression. Each is reached through machinery
// §37.49 and §37.52 draw - the assertion's location and name properties, its
// edges to the instance and to the clocking block, and the property
// specification's vpiClockingEvent edge - so these tests ask for the six items
// the way an application would and read what comes back.

// The nine kinds §39.3.2 lists under "assertion type".
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

// §39.3.2, "assertion type": the nine kinds the subclause lists are each an
// assertion, each reports itself through vpi_get(vpiType), and the type read
// back is the kind the assertion was written as rather than the class the nine
// belong to.
TEST_F(AssertionStaticInformationItems, EveryListedAssertionTypeReportsItself) {
  for (const AssertionKind& kind : kAssertionKinds) {
    VpiObject assertion;
    assertion.type = kind.type;

    EXPECT_EQ(vpi_get(vpiType, &assertion), kind.type) << kind.label;
    EXPECT_NE(vpi_get(vpiType, &assertion), vpiAssertion) << kind.label;
  }
}

// §39.3.2, "assertion name", "instance in which the assertion occurs", and
// "module definition containing the assertion": the name is the assertion's
// own, the instance is the one it is written in, and the definition that
// instance is an instance of is what names the module the assertion was written
// in - the same assertion in a second instance of that module reports the other
// instance and the same definition.
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

  EXPECT_STREQ(vpi_get_str(vpiName, &in_first), "handshake_p");
  EXPECT_EQ(vpi_handle(vpiInstance, &in_first), &first_instance);
  EXPECT_EQ(vpi_handle(vpiInstance, &in_second), &second_instance);
  EXPECT_STREQ(vpi_get_str(vpiDefName, vpi_handle(vpiInstance, &in_first)),
               "handshake");
  EXPECT_STREQ(vpi_get_str(vpiDefName, vpi_handle(vpiInstance, &in_second)),
               "handshake");
}

// §39.3.2, "assertion source information: the file, line, and column where the
// assertion is defined": §37.49 draws all three on the assertion's location,
// and the column is what separates two assertions written on one line.
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

  EXPECT_STREQ(vpi_get_str(vpiFile, &first), "handshake.sv");
  EXPECT_EQ(vpi_get(vpiStartLine, &first), 12);
  EXPECT_EQ(vpi_get(vpiColumn, &first), 5);
  EXPECT_EQ(vpi_get(vpiEndLine, &first), 12);
  EXPECT_EQ(vpi_get(vpiEndColumn, &first), 30);

  // Same file, same line: the column is the only thing that tells the two
  // assertions apart by where they were written.
  EXPECT_EQ(vpi_get(vpiStartLine, &second), vpi_get(vpiStartLine, &first));
  EXPECT_NE(vpi_get(vpiColumn, &second), vpi_get(vpiColumn, &first));
}

// §39.3.2, "assertion clocking block/expression", first half: §37.49 draws the
// assertion's edge to the clocking block that governs it, and an assertion
// governed by none reports none.
TEST_F(AssertionStaticInformationItems, TheClockingBlockGoverningTheAssertion) {
  VpiObject clocking;
  clocking.type = vpiClockingBlock;
  clocking.name = "cb";
  VpiObject clocked;
  clocked.type = vpiAssert;
  clocked.children = {&clocking};

  VpiObject unclocked;
  unclocked.type = vpiAssert;

  EXPECT_EQ(vpi_handle(vpiClockingBlock, &clocked), &clocking);
  EXPECT_EQ(vpi_handle(vpiClockingBlock, &unclocked), nullptr);
}

// §39.3.2, "assertion clocking block/expression", the other half: an assertion
// written with a clocking event of its own carries it on the property
// specification, which §37.52 draws the vpiClockingEvent edge from. The clocked
// property the specification may hold instead carries it the same way.
TEST_F(AssertionStaticInformationItems, TheClockingExpressionOfTheAssertion) {
  VpiObject event;
  event.type = vpiEventControl;
  VpiObject spec;
  spec.type = vpiPropertySpec;
  spec.children = {&event};

  VpiObject inner_event;
  inner_event.type = vpiEventControl;
  VpiObject clocked_property;
  clocked_property.type = vpiClockedProperty;
  clocked_property.children = {&inner_event};

  VpiObject unclocked_spec;
  unclocked_spec.type = vpiPropertySpec;

  EXPECT_EQ(vpi_handle(vpiClockingEvent, &spec), &event);
  EXPECT_EQ(vpi_handle(vpiClockingEvent, &clocked_property), &inner_event);
  EXPECT_EQ(vpi_handle(vpiClockingEvent, &unclocked_spec), nullptr);
}

}  // namespace
}  // namespace delta
