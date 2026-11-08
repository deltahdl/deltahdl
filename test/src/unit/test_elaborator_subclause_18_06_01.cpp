#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(StdClassBuiltInMethods, AHandleOfAStdClassCallsEveryClasssMethods) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  mailbox #(int) mb = new;\n"
             "  semaphore sem = new;\n"
             "  process p;\n"
             "  string s;\n"
             "  initial begin\n"
             "    p = process::self();\n"
             "    void'(mb.randomize());\n"
             "    void'(sem.randomize());\n"
             "    void'(p.randomize());\n"
             "    mb.pre_randomize();\n"
             "    sem.post_randomize();\n"
             "    mb.rand_mode(0);\n"
             "    p.constraint_mode(1);\n"
             "    sem.srandom(7);\n"
             "    s = mb.get_randstate();\n"
             "    sem.set_randstate(s);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(StdClassBuiltInMethods, TheActualsAreThoseTheMethodTakes) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  mailbox #(int) mb = new;\n"
      "  semaphore sem = new;\n"
      "  initial begin\n"
      "    sem.rand_mode();\n"
      "    mb.constraint_mode(0, 1);\n"
      "    mb.srandom();\n"
      "    sem.pre_randomize(1);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "method 'rand_mode' of class 'semaphore' takes at "
                            "least 1 argument; 0 given",
                            5, "18.8"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "method 'constraint_mode' of class 'mailbox' "
                            "takes at most 1 argument; 2 given",
                            6, "18.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "method 'srandom' of class 'mailbox' takes at "
                            "least 1 argument; 0 given",
                            7, "18.13.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "method 'pre_randomize' of class 'semaphore' "
                            "takes at most 0 arguments; 1 given",
                            8, "18.6.2"));
}

}  // namespace
