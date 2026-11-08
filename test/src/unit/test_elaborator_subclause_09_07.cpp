#include <gtest/gtest.h>

#include <initializer_list>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

TEST(FineGrainProcessControlElaboration, ProcessSelfElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    static process p = process::self();\n"
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

TEST(FineGrainProcessControlElaboration, ProcessNewInADeclarationError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  process q = new;\n"
             "  initial begin process p = new; end\n"
             "  process jobs[] = new [2];\n"
             "  initial begin process job[] = new [2]; end\n"
             "endmodule\n",
             f));
  const char* const kMessage = "cannot construct a process object with 'new'";
  for (const int kLine : {2, 3}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, kLine, "9.7"))
        << kLine;
  }
  for (const int kLine : {4, 5}) {
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kMessage, kLine, "9.7"))
        << kLine;
  }
}

TEST(FineGrainProcessControlElaboration, ProcessPassedToTaskElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task automatic do_work(process p);\n"
      "    p.kill();\n"
      "  endtask\n"
      "  initial begin\n"
      "    static process p = process::self();\n"
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
      "    static process p = process::self();\n"
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

TEST(FineGrainProcessControlElaboration, ModuleStateVariableNamesTheEnum) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  process::state ms;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* ms = FindVar(design, "m", "ms");
  ASSERT_NE(ms, nullptr);
  EXPECT_EQ(ms->width, 32u);
  EXPECT_EQ(ms->enum_type_name, "process::state");
}

}  // namespace
