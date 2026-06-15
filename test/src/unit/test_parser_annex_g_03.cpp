// IEEE 1800-2023 Annex G.3 (Std package -- Semaphore).
//
// The std-package `semaphore` prototype (G.3) introduces `semaphore` as a
// built-in class type. These tests observe the parser recognizing that
// std-package type name (Parser::known_types_ seeds "semaphore") so that
// declarations and the prototype's method calls parse without any user
// `class semaphore` definition. Semantics belong to clause 15.3.

#include "fixture_parser.h"

using namespace delta;

namespace {

// `semaphore` is a known std-package type name on its own.
TEST(SemaphoreStdPackageParser, BareDeclarationOfBuiltInType) {
  auto r = Parse(
      "module m;\n"
      "  semaphore sem;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
}

// The full prototype call surface parses: new / put / get / try_get, with the
// documented default arguments omitted.
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

// The prototype declares try_get as `function int`, so its result is a value
// and must parse in an expression position such as an if-condition.
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
