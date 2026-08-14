#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(FineGrainProcessControlElaboration, ProcessSelfElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    process p = process::self();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FineGrainProcessControlElaboration, ProcessMethodCallsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    process p;\n"
      "    p = process::self();\n"
      "    p.status();\n"
      "    p.kill();\n"
      "    p.suspend();\n"
      "    p.resume();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §9.7: the process class prototype lists srandom()/get_randstate()/
// set_randstate() as members (their RNG semantics are §18.13.3/.4/.5). Calling
// them on a process handle -- including reading a state string and feeding it
// back -- elaborates without error, i.e. the process class exposes these
// members alongside the control methods.
TEST(FineGrainProcessControlElaboration, ProcessRandStateMethodsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string s;\n"
      "  initial begin\n"
      "    process p;\n"
      "    p = process::self();\n"
      "    p.srandom(7);\n"
      "    s = p.get_randstate();\n"
      "    p.set_randstate(s);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FineGrainProcessControlElaboration, ProcessInForkElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    process p;\n"
      "    fork\n"
      "      begin\n"
      "        p = process::self();\n"
      "      end\n"
      "    join_none\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §9.7 gives the prototype as `class :final process;` and states that the
// process class cannot be extended. The report names §8.13, which is the
// clause stating that a class declared `:final` cannot be extended, because
// that is the rule the extension breaks; §9.7 is what makes process `:final`.
TEST(FineGrainProcessControlElaboration, ExtendProcessError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C extends process;\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot extend a class declared ':final'", 1,
                            "8.13"));
}

// §9.7: objects of type process are created internally when processes are
// spawned, so a call to new on a process handle is an error. The report stands
// at the assignment, not at the declaration of the handle.
TEST(FineGrainProcessControlElaboration, ProcessNewError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  initial begin\n"
             "    process p;\n"
             "    p = new;\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot construct a process object with 'new'", 4,
                            "9.7"));
}

TEST(FineGrainProcessControlElaboration, ProcessPassedToTaskElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task automatic do_work(process p);\n"
      "    p.kill();\n"
      "  endtask\n"
      "  initial begin\n"
      "    process p = process::self();\n"
      "    do_work(p);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FineGrainProcessControlElaboration, ProcessAwaitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    process p;\n"
      "    fork\n"
      "      begin\n"
      "        p = process::self();\n"
      "        #10;\n"
      "      end\n"
      "    join_none\n"
      "    p.await();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FineGrainProcessControlElaboration, AllStateEnumMembersElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    process p = process::self();\n"
      "    if (p.status() == process::FINISHED) ;\n"
      "    if (p.status() == process::RUNNING) ;\n"
      "    if (p.status() == process::WAITING) ;\n"
      "    if (p.status() == process::SUSPENDED) ;\n"
      "    if (p.status() == process::KILLED) ;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
