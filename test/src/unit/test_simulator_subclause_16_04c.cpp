#include <gtest/gtest.h>

#include <initializer_list>
#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

const char kReactiveWrite[] = "    assert #0 (1) setr(r, 20);\n";

std::string Top(const std::string& assertion, const std::string& after = "") {
  return "class C;\n"
         "  task automatic t(ref int x); x = 31; endtask\n"
         "  function automatic void fr(const ref int x); "
         "$display(\"C.fr %0d\", x); endfunction\n"
         "endclass\n"
         "module top;\n"
         "  int r = 0; int fa [2] = '{0, 0}; C h = new;\n"
         "  task automatic show(ref int x, input string w); "
         "$display(\"%s %0d\", w, x); endtask\n"
         "  task automatic cshow(const ref int x, input string w); "
         "$display(\"%s %0d\", w, x); endtask\n"
         "  function automatic void vcshow(const ref int x, input string w); "
         "$display(\"%s %0d\", w, x); endfunction\n"
         "  task automatic setr(ref int x, input int n); x = n; endtask\n"
         "  function automatic void vsetr(ref int x, input int n); x = n; "
         "endfunction\n"
         "  initial begin\n"
         "    r = 1; fa[1] = 1;\n"
         "    " +
         assertion +
         "\n"
         "    r = 2; r <= 3; fa[1] = 2; fa[1] <= 3;\n" +
         after +
         "  end\n"
         "endmodule\n";
}

std::string Simulate(const std::string& src) {
  SimFixture f;
  std::string out = RunCapture(src, f);
  EXPECT_FALSE(f.diag.HasErrors()) << src;
  return out;
}

struct Case {
  const char* assertion;
  const char* expected;
};

void ExpectReactive(std::initializer_list<Case> cases) {
  for (const auto& c : cases) {
    EXPECT_EQ(Simulate(Top(c.assertion)), c.expected) << c.assertion;
  }
}

void ExpectPostponed(std::initializer_list<Case> cases) {
  for (const auto& c : cases) {
    EXPECT_EQ(Simulate(Top(c.assertion, kReactiveWrite)), c.expected)
        << c.assertion;
  }
}

TEST(DeferredRefActualRegion, AnObservedFailActionReadsTheReactiveValue) {
  ExpectReactive({{"assert #0 (0) else show(r, \"f\");", "f 3\n"}});
}

TEST(DeferredRefActualRegion, AFinalFailActionReadsThePostponedValue) {
  ExpectPostponed({{"assert final (0) else show(r, \"f\");", "f 20\n"}});
}

TEST(DeferredRefActualRegion, AnObservedAssumeOrCoverReadsTheReactiveValue) {
  ExpectReactive({{"assume #0 (1) show(r, \"a\");", "a 3\n"},
                  {"assume #0 (0) else show(r, \"a\");", "a 3\n"},
                  {"cover #0 (1) show(r, \"c\");", "c 3\n"}});
}

TEST(DeferredRefActualRegion, AFinalAssumeOrCoverReadsThePostponedValue) {
  ExpectPostponed({{"assume final (1) show(r, \"a\");", "a 20\n"},
                   {"assume final (0) else show(r, \"a\");", "a 20\n"},
                   {"cover final (1) show(r, \"c\");", "c 20\n"}});
}

TEST(DeferredRefActualRegion, AConstRefActualIsReadInTheActionsRegion) {
  ExpectReactive({{"assert #0 (1) cshow(r, \"t\");", "t 3\n"},
                  {"assert #0 (0) else vcshow(r, \"v\");", "v 3\n"}});
  ExpectPostponed({{"assert final (1) cshow(r, \"t\");", "t 20\n"},
                   {"assert final (0) else vcshow(r, \"v\");", "v 20\n"}});
}

TEST(DeferredRefActualRegion, AnObservedActionAssignsThroughItsRefFormal) {
  for (const char* assertion :
       {"assert #0 (1) setr(r, 5);", "assert #0 (0) else setr(r, 5);",
        "assume #0 (1) setr(r, 5);", "cover #0 (1) setr(r, 5);",
        "assert #0 (1) vsetr(r, 5);", "assume #0 (0) else vsetr(r, 5);"}) {
    EXPECT_EQ(Simulate(Top(assertion,
                           "    assert final (1) show(r, \"fin\");\n"
                           "    #1 $display(\"end %0d\", r);\n")),
              "fin 5\nend 5\n")
        << assertion;
  }
}

TEST(DeferredRefActualRegion, AMethodWritesOrReadsThroughItsRefFormal) {
  EXPECT_EQ(
      Simulate(Top("assert #0 (1) h.t(r);", "    assert final (1) h.fr(r);\n")),
      "C.fr 31\n");
}

TEST(DeferredRefActualRegion, AnArrayElementIsReadInTheActionsRegion) {
  ExpectReactive({{"assert #0 (1) show(fa[1], \"e\");", "e 3\n"}});
  EXPECT_EQ(Simulate(Top("assert final (0) else cshow(fa[1], \"e\");",
                         "    assert #0 (1) setr(fa[1], 20);\n")),
            "e 20\n");
}

TEST(DeferredRefActualRegion, AStaticAssertionsActionReadsItsRegionsValue) {
  const std::string kHead =
      "module top;\n"
      "  logic c = 1; int r = 0;\n"
      "  task automatic show(const ref int x, input string w); "
      "$display(\"%s %0d\", w, x); endtask\n"
      "  task automatic setr(ref int x, input int n); x = n; endtask\n";
  EXPECT_EQ(
      Simulate(kHead + "  a: assert #0 (c) else show(r, \"s\");\n"
                       "  initial begin #1 r = 1; c = 0; r = 2; r <= 3; end\n"
                       "endmodule\n"),
      "s 3\n");
  EXPECT_EQ(Simulate(kHead + "  b: assert final (c) else show(r, \"s\");\n"
                             "  initial begin #1 r = 1; c = 0; r = 2; r <= 3;\n"
                             "    assert #0 (1) setr(r, 20); end\n"
                             "endmodule\n"),
            "s 20\n");
}

}  // namespace
