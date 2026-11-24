#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

namespace {

std::string OutputOf(const std::string& steps) {
  SimFixture f;
  return RunCapture("module t;\n  process::state s;\n" + steps + "endmodule\n",
                    f);
}

TEST(ProcessPrototypeRun, EachStateMemberHasItsPlaceAsItsValue) {
  EXPECT_EQ(OutputOf("  initial $write(\"%0d %0d %0d %0d %0d\",\n"
                     "    process::FINISHED, process::RUNNING,\n"
                     "    process::WAITING, process::SUSPENDED,\n"
                     "    process::KILLED);\n"),
            "0 1 2 3 4");
}

TEST(ProcessPrototypeRun, DISABLED_TheStateTypeIsSigned) {
  EXPECT_EQ(OutputOf("  initial $write(\"%0d\", process::state'(-1) < 0);\n"),
            "1");
}

TEST(ProcessPrototypeRun, TheStateMembersAreInDeclaredOrder) {
  EXPECT_EQ(OutputOf("  initial $write(\"%s %s %0d\", s.first().name(),\n"
                     "    s.last().name(), s.num());\n"),
            "FINISHED KILLED 5");
}

TEST(ProcessPrototypeRun, AStateVariableIsThirtyTwoBits) {
  EXPECT_EQ(OutputOf("  initial $write(\"%0d\", $bits(s));\n"), "32");
}

TEST(ProcessPrototypeRun, DISABLED_TheStateTypeIsThirtyTwoBits) {
  EXPECT_EQ(OutputOf("  initial $write(\"%0d %0d\", $bits(process::state),\n"
                     "    $bits(std::process::state));\n"),
            "32 32");
}

TEST(ProcessPrototypeRun, SelfThroughTheClassIsTheCallingProcess) {
  EXPECT_EQ(OutputOf("  initial begin\n"
                     "    process p;\n"
                     "    p = process::self();\n"
                     "    $write(\"%0d %0d\", p == process::self(),\n"
                     "           p == std::process::self());\n"
                     "  end\n"),
            "1 1");
}

TEST(ProcessPrototypeRun, DISABLED_SelfThroughAHandleIsTheCallingProcess) {
  EXPECT_EQ(OutputOf("  process other;\n"
                     "  initial begin\n"
                     "    other = process::self();\n"
                     "    #5;\n"
                     "  end\n"
                     "  initial begin\n"
                     "    process p, none;\n"
                     "    #1 p = process::self();\n"
                     "    $write(\"%0d %0d\", p == p.self(),\n"
                     "           p == none.self());\n"
                     "    $write(\" %0d %0d\", p == other.self(),\n"
                     "           other == other.self());\n"
                     "  end\n"),
            "1 1 1 0");
}

}  // namespace
