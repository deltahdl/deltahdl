#include "fixture_program.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"
#include "parser/assertion_control_task.h"

using namespace delta;

namespace {

TEST_F(ApiParseTest, AssertOnSystemCall) {
  auto* unit = Parse(R"(
    module m;
      initial $assertOn;
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST_F(ApiParseTest, AssertOffSystemCall) {
  auto* unit = Parse(R"(
    module m;
      initial $assertOff;
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST_F(ApiParseTest, AssertKillSystemCall) {
  auto* unit = Parse(R"(
    module m;
      initial $assertKill;
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST(AssertionApiParsing, AssertOnNoArgs) {
  auto r = Parse(R"(
    module m;
      initial $asserton;
    endmodule
  )");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(AssertionApiParsing, AssertOffNoArgs) {
  auto r = Parse(R"(
    module m;
      initial $assertoff;
    endmodule
  )");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(AssertionApiParsing, AssertKillNoArgs) {
  auto r = Parse(R"(
    module m;
      initial $assertkill;
    endmodule
  )");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(AssertionApiParsing, AssertOnWithLevelArg) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      initial $asserton(0);
    endmodule
  )"));
}

TEST(AssertionApiParsing, AssertOffWithLevelAndModuleArgs) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      initial $assertoff(0, m);
    endmodule
  )"));
}

TEST(AssertionApiParsing, AssertControlSystemTask) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      initial $assertcontrol(3);
    endmodule
  )"));
}

TEST(AssertionApiParsing, AssertPassStepAndFailStep) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      initial begin
        $assertpasson;
        $assertpassoff;
      end
    endmodule
  )"));
}

TEST(AssertionApiParsing, AssertionControlInAlwaysBlock) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      logic clk, reset;
      always @(posedge clk) begin
        if (reset)
          $assertoff(0, m);
        else
          $asserton(0, m);
      end
    endmodule
  )"));
}

TEST(AssertionApiParsing, AssertionControlSequence) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      initial begin
        $assertoff;
        $assertkill;
        #100;
        $asserton;
      end
    endmodule
  )"));
}

// §20.11 (Syntax 20-12): the remaining assert_action_task names and a fully
// argumented $assertcontrol parse as system task calls.
TEST(AssertionApiParsing, AssertActionTasksAndAssertControl) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      initial begin
        $assertfailon;
        $assertfailoff;
        $assertnonvacuouson;
        $assertvacuousoff;
        $assertcontrol(3, 15, 7, 0);
      end
    endmodule
  )"));
}

// §20.11 (Syntax 20-12): assert_task names ($asserton, $assertoff, $assertkill)
// are classified as the assert_task category.
TEST(AssertionControlGrammar, ClassifiesAssertTask) {
  EXPECT_EQ(ClassifyAssertionControlTask("$asserton"),
            AssertionControlTaskCategory::kAssertTask);
  EXPECT_EQ(ClassifyAssertionControlTask("$assertoff"),
            AssertionControlTaskCategory::kAssertTask);
  EXPECT_EQ(ClassifyAssertionControlTask("$assertkill"),
            AssertionControlTaskCategory::kAssertTask);
}

// §20.11 (Syntax 20-12): the six action control tasks are classified as the
// assert_action_task category.
TEST(AssertionControlGrammar, ClassifiesAssertActionTask) {
  EXPECT_EQ(ClassifyAssertionControlTask("$assertpasson"),
            AssertionControlTaskCategory::kAssertActionTask);
  EXPECT_EQ(ClassifyAssertionControlTask("$assertvacuousoff"),
            AssertionControlTaskCategory::kAssertActionTask);
}

// §20.11 (Syntax 20-12): $assertcontrol is its own category, and an unrelated
// system task is not an assertion control task.
TEST(AssertionControlGrammar, ClassifiesAssertControlAndRejectsOthers) {
  EXPECT_EQ(ClassifyAssertionControlTask("$assertcontrol"),
            AssertionControlTaskCategory::kAssertControl);
  EXPECT_TRUE(IsAssertionControlTaskName("$assertcontrol"));
  EXPECT_FALSE(IsAssertionControlTaskName("$display"));
}

// §20.11 (Syntax 20-12): list_of_scopes_or_assertions is a comma-separated
// list, so an assert_task may name several scopes after the levels argument.
TEST(AssertionApiParsing, AssertTaskWithScopeList) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      logic clk;
      initial $assertoff(0, a, b, c);
    endmodule
  )"));
}

// §20.11 (Syntax 20-12): scope_or_assertion is a hierarchical_identifier, so a
// dotted name is accepted in the scope list of $assertcontrol.
TEST(AssertionApiParsing, AssertControlWithHierarchicalScope) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      initial $assertcontrol(5, 15, 7, 0, top.sub.chk);
    endmodule
  )"));
}

}  // namespace
