#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// 18.14.1 initialization RNG: each module instance has one, seeded with the
// default seed, from which its static processes are seeded each with the next
// value and the objects its static declaration initializers create are
// seeded, so the first static process of two instances of one module draws
// alike, so does the object each instance's declaration creates, and two
// static processes of one instance differ, as the design
// test/src/e2e/random_stability_properties.sv runs it.
TEST(RandomStabilityPropertiesRun,
     TheInitializationRngOfEachInstanceIsSeededAlike) {
  SimFixture f;
  std::string out = RunCapture(
      "module stable_leaf;\n"
      "  class Item;\n"
      "    rand bit [15:0] payload;\n"
      "  endclass\n"
      "  Item sp = new;\n"
      "  int unsigned first, second;\n"
      "  bit [15:0] sp_payload;\n"
      "  int k;\n"
      "  initial first = $urandom;\n"
      "  initial second = $urandom;\n"
      "  initial begin k = sp.randomize(); sp_payload = sp.payload; end\n"
      "endmodule\n"
      "module t;\n"
      "  stable_leaf u1();\n"
      "  stable_leaf u2();\n"
      "  int same_first, same_object, distinct;\n"
      "  initial begin\n"
      "    #1;\n"
      "    same_first = u1.first == u2.first;\n"
      "    same_object = u1.sp_payload == u2.sp_payload;\n"
      "    distinct = u1.first != u1.second;\n"
      "    $display(\"%0d %0d %0d\", same_first, same_object, distinct);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1 1\n");
}

// 18.14.1 thread stability: a new dynamic thread's RNG is seeded with the
// next random value of its parent thread, so a forked thread seeded by hand
// with the value the parent would have drawn next draws the same four values
// as one the fork seeded, and a thread added at the end of a fork leaves the
// earlier two drawing as before, as the design
// test/src/e2e/random_stability_properties.sv runs it.
TEST(RandomStabilityPropertiesRun,
     AForkedThreadIsSeededWithTheParentsNextValue) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  process p;\n"
      "  int i, alike = 0, kept = 0;\n"
      "  int unsigned seedv, ca[4], cm[4], f1, f2, g1, g2, g3;\n"
      "  initial begin\n"
      "    p = process::self();\n"
      "    p.srandom(21);\n"
      "    fork\n"
      "      begin\n"
      "        for (int j = 0; j < 4; j++) ca[j] = $urandom;\n"
      "      end\n"
      "    join\n"
      "    p.srandom(21);\n"
      "    seedv = $urandom;\n"
      "    fork\n"
      "      begin\n"
      "        process q = process::self();\n"
      "        q.srandom(seedv);\n"
      "        for (int j = 0; j < 4; j++) cm[j] = $urandom;\n"
      "      end\n"
      "    join\n"
      "    for (i = 0; i < 4; i++) if (ca[i] == cm[i]) alike++;\n"
      "    p.srandom(21);\n"
      "    fork\n"
      "      f1 = $urandom;\n"
      "      f2 = $urandom;\n"
      "    join\n"
      "    p.srandom(21);\n"
      "    fork\n"
      "      g1 = $urandom;\n"
      "      g2 = $urandom;\n"
      "      g3 = $urandom;\n"
      "    join\n"
      "    if (f1 == g1) kept++;\n"
      "    if (f2 == g2) kept++;\n"
      "    $display(\"%0d %0d\", alike, kept);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4 2\n");
}

// 18.14.1 object stability: an object created with new is seeded with the
// next random value of the creating thread, so an object seeded by hand with
// the value the thread would have drawn next draws the same four values as
// one new seeded, and objects created after it leave its draw as before, as
// the design test/src/e2e/random_stability_properties.sv runs it.
TEST(RandomStabilityPropertiesRun,
     AnObjectIsSeededWithTheCreatingThreadsNextValue) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class Packet;\n"
      "    rand bit [15:0] payload;\n"
      "  endclass\n"
      "  Packet a, b, c, d;\n"
      "  process p;\n"
      "  int i, k, alike = 0, kept;\n"
      "  int unsigned seedv;\n"
      "  bit [15:0] sa[4], sm[4];\n"
      "  initial begin\n"
      "    p = process::self();\n"
      "    p.srandom(33);\n"
      "    a = new;\n"
      "    for (i = 0; i < 4; i++) begin k = a.randomize(); sa[i] = "
      "a.payload; end\n"
      "    p.srandom(33);\n"
      "    seedv = $urandom;\n"
      "    b = new;\n"
      "    b.srandom(seedv);\n"
      "    for (i = 0; i < 4; i++) begin k = b.randomize(); sm[i] = "
      "b.payload; end\n"
      "    for (i = 0; i < 4; i++) if (sa[i] == sm[i]) alike++;\n"
      "    p.srandom(33);\n"
      "    a = new; c = new; d = new;\n"
      "    k = a.randomize();\n"
      "    kept = a.payload == sa[0];\n"
      "    $display(\"%0d %0d\", alike, kept);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4 1\n");
}

// 18.14.1 manual seeding: every noninitialization RNG can be seeded by hand,
// and with hierarchical seeding one seed at the root thread defines the whole
// subtree, so the root seeded with 44 again replays two forked threads that
// each create an object, randomize it and draw $urandom, as the design
// test/src/e2e/random_stability_properties.sv runs it.
TEST(RandomStabilityPropertiesRun, OneSeedAtTheRootDefinesTheForkedSubtree) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class Packet;\n"
      "    rand bit [15:0] payload;\n"
      "  endclass\n"
      "  process p;\n"
      "  int i, k, replayed = 0;\n"
      "  int unsigned m1[4], m2[4];\n"
      "  initial begin\n"
      "    p = process::self();\n"
      "    p.srandom(44);\n"
      "    fork\n"
      "      begin Packet o = new; k = o.randomize(); m1[0] = o.payload; "
      "m1[1] = $urandom; end\n"
      "      begin Packet o = new; k = o.randomize(); m1[2] = o.payload; "
      "m1[3] = $urandom; end\n"
      "    join\n"
      "    p.srandom(44);\n"
      "    fork\n"
      "      begin Packet o = new; k = o.randomize(); m2[0] = o.payload; "
      "m2[1] = $urandom; end\n"
      "      begin Packet o = new; k = o.randomize(); m2[2] = o.payload; "
      "m2[3] = $urandom; end\n"
      "    join\n"
      "    for (i = 0; i < 4; i++) if (m1[i] == m2[i]) replayed++;\n"
      "    $display(\"%0d\", replayed);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4\n");
}

}  // namespace
