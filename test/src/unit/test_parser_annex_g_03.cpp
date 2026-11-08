#include <gtest/gtest.h>

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(SemaphoreStdPackageParser, BareDeclarationOfBuiltInType) {
  auto r = Parse(
      "module m;\n"
      "  semaphore sem;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
}

TEST(SemaphoreStdPackageParser, PrototypeMethodsParseWithDefaults) {
  auto r = Parse(
      "module m;\n"
      "  semaphore sem = new();\n"
      "  int got;\n"
      "  initial begin\n"
      "    sem.put();\n"
      "    sem.get();\n"
      "    got = sem.try_get();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
}

TEST(SemaphoreStdPackageParser, TryGetResultUsableInCondition) {
  auto r = Parse(
      "module m;\n"
      "  semaphore sem = new();\n"
      "  initial begin\n"
      "    if (sem.try_get()) sem.put();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
