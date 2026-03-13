#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

namespace {

// §15.3: semaphore is a built-in class; verify bare declaration parses.
TEST(SemaphoreParser, BareDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  semaphore smTx;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
}

// §15.3: semaphore declaration with new() constructor and method calls.
TEST(SemaphoreParser, DeclarationWithNewAndMethodCalls) {
  auto r = Parse(
      "module m;\n"
      "  semaphore sem = new(1);\n"
      "  initial begin\n"
      "    sem.get();\n"
      "    sem.put();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
}

// §15.3: all four semaphore methods parse in procedural context.
TEST_F(AnnexHParseTest, MethodCallsInInitialBlock) {
  auto* unit = Parse(
      "module m;\n"
      "  initial begin\n"
      "    sem.get(1);\n"
      "    sem.put(1);\n"
      "    if (sem.try_get(1)) begin\n"
      "      $display(\"acquired\");\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  EXPECT_FALSE(diag_.HasErrors());
}

// §15.3: multiple semaphore declarations in one module.
TEST(SemaphoreParser, MultipleSemaphoreDeclarations) {
  auto r = Parse(
      "module m;\n"
      "  semaphore mutex;\n"
      "  semaphore resource_lock;\n"
      "  semaphore sync_sem;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
}

// §15.3: semaphore is recognized as a type without a class declaration.
TEST(SemaphoreParser, NoClassDeclarationRequired) {
  auto r = Parse(
      "module m;\n"
      "  semaphore s;\n"
      "  initial begin\n"
      "    s = new();\n"
      "    s.put(2);\n"
      "    s.get();\n"
      "    if (s.try_get()) $display(\"ok\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
