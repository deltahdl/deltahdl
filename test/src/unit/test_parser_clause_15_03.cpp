#include "fixture_parser.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// §15.3 Semaphores — Parser coverage
// ---------------------------------------------------------------------------

TEST(SemaphoreParser, DeclarationWithNew) {
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

TEST(SemaphoreParser, NewExpression) {
  // §15.3.1: Semaphore constructed via new() expression.
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    smTx = new(1);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
}

TEST(SemaphoreParser, NewDefaultKeyCount) {
  // §15.3.1: Default keyCount is 0.
  auto r = Parse(
      "module m;\n"
      "  semaphore sem = new();\n"
      "  initial begin\n"
      "    sem.put(1);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SemaphoreParser, AllMethodCalls) {
  // §15.3.2/3/4: get(), put(), try_get() method calls.
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    sem.get(1);\n"
      "    sem.put(1);\n"
      "    if (sem.try_get(1)) begin\n"
      "      $display(\"acquired\");\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
}

TEST(SemaphoreParser, MethodCallDefaultArgs) {
  // §15.3: All methods have default keyCount = 1.
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    sem.get();\n"
      "    sem.put();\n"
      "    sem.try_get();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SemaphoreParser, TryGetInConditional) {
  // §15.3.4: try_get() returns int, usable in conditions.
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (sem.try_get()) begin\n"
      "      $display(\"got key\");\n"
      "    end else begin\n"
      "      $display(\"no key\");\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SemaphoreParser, MultipleDeclarations) {
  auto r = Parse(
      "module m;\n"
      "  semaphore s1 = new(0);\n"
      "  semaphore s2 = new(5);\n"
      "  initial begin\n"
      "    s1.put(1);\n"
      "    s2.get(2);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SemaphoreParser, MethodCallWithExpression) {
  // Method args can be arbitrary expressions.
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    sem.get(a + b);\n"
      "    sem.put(2 * n);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
