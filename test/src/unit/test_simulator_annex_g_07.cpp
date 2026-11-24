#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

namespace {

std::string ResultsOf(const std::string& steps) {
  SimFixture f;
  return RunCapture(
      "class C;\n  int x = 7;\nendclass\n"
      "class W extends weak_reference#(C);\n"
      "  function new(C o);\n    super.new(o);\n  endfunction\nendclass\n"
      "module t;\n  C c = new;\n  weak_reference #(C) wr;\n"
      "  initial begin\n" +
          steps + "  end\nendmodule\n",
      f);
}

TEST(WeakReferencePrototypeRun, AnActualIsBoundToReferentByName) {
  EXPECT_EQ(
      ResultsOf("wr = new(.referent(c));\n"
                "$write(\"%0d %0d\", wr.get() == c, wr.get() == null);\n"),
      "1 0");
}

TEST(WeakReferencePrototypeRun, ALocalsActualIsBoundToReferentByName) {
  EXPECT_EQ(ResultsOf("begin\n"
                      "  automatic weak_reference #(C) own =\n"
                      "      new(.referent(c));\n"
                      "  $write(\"%0d\", own.get() == c);\n"
                      "end\n"),
            "1");
}

TEST(WeakReferencePrototypeRun, AnActualIsBoundToObjByName) {
  EXPECT_EQ(ResultsOf("$write(\"%0d %0d\",\n"
                      "  weak_reference#(C)::get_id(.obj(c)) != 0,\n"
                      "  weak_reference#(C)::get_id(.obj(c)) ==\n"
                      "      weak_reference#(C)::get_id(c));\n"),
            "1 1");
}

TEST(WeakReferencePrototypeRun, AnIdentifierIsSixtyFourBits) {
  EXPECT_EQ(
      ResultsOf("$write(\"%0d\", $bits(weak_reference#(C)::get_id(c)));\n"),
      "64");
}

TEST(WeakReferencePrototypeRun, DISABLED_AnIdentifierIsSigned) {
  EXPECT_EQ(ResultsOf("$write(\"%0d\", weak_reference#(C)::get_id(c) > -1);\n"),
            "1");
}

TEST(WeakReferencePrototypeRun, DISABLED_GetIdIsCalledThroughAHandle) {
  EXPECT_EQ(ResultsOf("wr = new(c);\n"
                      "$write(\"%0d %0d\",\n"
                      "  wr.get_id(c) == weak_reference#(C)::get_id(c),\n"
                      "  wr.get_id(c) != 0);\n"),
            "1 1");
}

TEST(WeakReferencePrototypeRun, DISABLED_ADerivedClassInheritsGetAndClear) {
  EXPECT_EQ(ResultsOf("begin\n"
                      "  automatic W w = new(c);\n"
                      "  $write(\"%0d\", w.get() == c);\n"
                      "  w.clear();\n"
                      "  $write(\" %0d\", w.get() == null);\n"
                      "end\n"),
            "1 1");
}

}  // namespace
