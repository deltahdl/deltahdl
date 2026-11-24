#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

namespace {

std::string Printed(const std::string& items, const std::string& statements,
                    const std::string& before = "") {
  SimFixture f;
  return RunCapture(before +
                        "module t;\n"
                        "  int x, y;\n" +
                        items + "  initial begin\n" + statements +
                        "    $write(\"%0d %0d\", x, y);\n"
                        "  end\n"
                        "endmodule\n",
                    f);
}

std::string KeysOf(const std::string& statements) {
  return Printed("  semaphore s = new(0);\n  logic [3:0] unknown = 'x;\n",
                 statements +
                     "    repeat (20) if (s.try_get(1)) x++;\n"
                     "    y = s.try_get(1);\n");
}

TEST(SemaphorePrototypeRun, AConstructorWithoutAnActualMakesNoKey) {
  EXPECT_EQ(KeysOf("    s = new();\n"), "0 0");
  EXPECT_EQ(KeysOf("    s = new;\n"), "0 0");
  EXPECT_EQ(KeysOf("    s = new(3);\n"), "3 0");
}

TEST(SemaphorePrototypeRun, AnOmittedCountIsOneKey) {
  EXPECT_EQ(KeysOf("    s.put();\n    s.put;\n"), "2 0");
  EXPECT_EQ(KeysOf("    s = new(5);\n    s.get();\n    s.get;\n"), "3 0");
  EXPECT_EQ(KeysOf("    s = new(5);\n    void'(s.try_get());\n"), "4 0");
}

TEST(SemaphorePrototypeRun, AnActualIsBoundToKeyCountByName) {
  EXPECT_EQ(KeysOf("    s = new(.keyCount(3));\n"), "3 0");
  EXPECT_EQ(KeysOf("    s.put(.keyCount(4));\n"), "4 0");
  EXPECT_EQ(KeysOf("    s = new(5);\n    s.get(.keyCount(2));\n"), "3 0");
  EXPECT_EQ(KeysOf("    s = new(5);\n    void'(s.try_get(.keyCount(3)));\n"),
            "2 0");
}

TEST(SemaphorePrototypeRun, AWideOrUnknownActualIsConvertedToInt) {
  EXPECT_EQ(KeysOf("    s = new(34'h1_0000_0002);\n"), "2 0");
  EXPECT_EQ(KeysOf("    s.put(34'h1_0000_0003);\n"), "3 0");
  EXPECT_EQ(KeysOf("    s = new(5);\n    s.get(34'h1_0000_0002);\n"), "3 0");
  EXPECT_EQ(KeysOf("    s = new(5);\n    x = s.try_get(34'h1_0000_0002);\n"),
            "4 0");
  EXPECT_EQ(KeysOf("    s = new(unknown);\n"), "0 0");
  EXPECT_EQ(KeysOf("    s.put(unknown);\n    s.put(2);\n"), "2 0");
}

TEST(SemaphorePrototypeRun, DISABLED_ARealActualOfTheConstructorIsRounded) {
  EXPECT_EQ(KeysOf("    s = new(2.0);\n"), "2 0");
  EXPECT_EQ(KeysOf("    s = new(1.6);\n"), "2 0");
  EXPECT_EQ(KeysOf("    s = new(1.4);\n"), "1 0");
}

TEST(SemaphorePrototypeRun, DISABLED_ARealActualOfPutIsRounded) {
  EXPECT_EQ(KeysOf("    s.put(2.6);\n"), "3 0");
  EXPECT_EQ(KeysOf("    s.put(2.4);\n"), "2 0");
}

TEST(SemaphorePrototypeRun, DISABLED_ARealActualOfGetIsRounded) {
  EXPECT_EQ(KeysOf("    s.put(5);\n    s.get(1.6);\n"), "3 0");
  EXPECT_EQ(KeysOf("    s.put(5);\n    s.get(1.4);\n"), "4 0");
}

TEST(SemaphorePrototypeRun, DISABLED_ARealActualOfTryGetIsRounded) {
  EXPECT_EQ(KeysOf("    s.put(1);\n    y = s.try_get(1.6);\n    x = 10 * y;\n"),
            "1 0");
  EXPECT_EQ(KeysOf("    s.put(5);\n    void'(s.try_get(1.6));\n"), "3 0");
}

TEST(SemaphorePrototypeRun, TheResultOfTryGetIsThirtyTwoBits) {
  EXPECT_EQ(Printed("  semaphore s = new(0);\n",
                    "    x = $bits(s.try_get());\n"
                    "    y = s.try_get() - 1;\n"),
            "32 -1");
}

TEST(SemaphorePrototypeRun, DISABLED_TheResultOfTryGetIsSigned) {
  EXPECT_EQ(Printed("  semaphore s = new(0);\n",
                    "    x = (s.try_get() - 1) < 0;\n"
                    "    y = s.try_get() > -1;\n"),
            "1 1");
}

TEST(SemaphorePrototypeRun, AVoidCastOfTryGetTakesTheKey) {
  EXPECT_EQ(Printed("  semaphore s = new(1);\n",
                    "    void'(s.try_get());\n"
                    "    x = 7;\n"
                    "    y = s.try_get();\n"),
            "7 0");
}

TEST(SemaphorePrototypeRun, AForkedGetInAFunctionTakesTheKey) {
  EXPECT_EQ(Printed("  semaphore s = new(3);\n"
                    "  function automatic int take();\n"
                    "    fork\n"
                    "      s.get(2);\n"
                    "    join_none\n"
                    "    return 5;\n"
                    "  endfunction\n",
                    "    x = take();\n"
                    "    #1;\n"
                    "    y = s.try_get(2) * 10 + s.try_get(1);\n"),
            "5 1");
}

TEST(SemaphorePrototypeRun, AProgramsSemaphoreHoldsItsKeys) {
  SimFixture f;
  EXPECT_EQ(RunCapture("program t;\n"
                       "  std::semaphore q = new(1);\n"
                       "  semaphore s = new(2);\n"
                       "  initial begin\n"
                       "    $write(\"%0d\", q.try_get(2));\n"
                       "    $write(\"%0d\", q.try_get());\n"
                       "    $write(\"%0d\", s.try_get(2));\n"
                       "  end\n"
                       "endprogram\n",
                       f),
            "011");
}

TEST(SemaphorePrototypeRun, AUnitsSemaphoreHoldsItsKeys) {
  EXPECT_EQ(Printed("",
                    "    x = unit_keys.try_get(3);\n"
                    "    y = unit_keys.try_get(2);\n",
                    "semaphore unit_keys = new(2);\n"),
            "0 1");
}

}  // namespace
